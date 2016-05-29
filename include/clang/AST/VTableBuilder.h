//===--- VTableBuilder.h - C++ vtable layout builder --------------*- C++ -*-=//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This contains code dealing with generation of the layout of virtual tables.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_VTABLEBUILDER_H
#define LLVM_CLANG_AST_VTABLEBUILDER_H

#include "clang/AST/BaseSubobject.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/GlobalDecl.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Basic/ABI.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"
#include <memory>
#include <utility>

namespace clang {
  class CXXRecordDecl;

/// \brief Represents a single component in a vtable.
class VTableComponent {
public:
  enum Kind {
    CK_VCallOffset,
    CK_VBaseOffset,
    CK_OffsetToTop,
    CK_RTTI,
    CK_FunctionPointer,

    /// \brief A pointer to the complete destructor.
    CK_CompleteDtorPointer,

    /// \brief A pointer to the deleting destructor.
    CK_DeletingDtorPointer,

    /// \brief An entry that is never used.
    ///
    /// In some cases, a vtable function pointer will end up never being
    /// called. Such vtable function pointers are represented as a
    /// CK_UnusedFunctionPointer.
    CK_UnusedFunctionPointer
  };

  VTableComponent() = default;

  static VTableComponent MakeVCallOffset(CharUnits Offset) {
    return VTableComponent(CK_VCallOffset, Offset);
  }

  static VTableComponent MakeVBaseOffset(CharUnits Offset) {
    return VTableComponent(CK_VBaseOffset, Offset);
  }

  static VTableComponent MakeOffsetToTop(CharUnits Offset) {
    return VTableComponent(CK_OffsetToTop, Offset);
  }

  static VTableComponent MakeRTTI(const CXXRecordDecl *RD) {
    return VTableComponent(CK_RTTI, reinterpret_cast<uintptr_t>(RD));
  }

  static VTableComponent MakeFunction(const CXXMethodDecl *MD) {
    assert(!isa<CXXDestructorDecl>(MD) &&
           "Don't use MakeFunction with destructors!");

    return VTableComponent(CK_FunctionPointer,
                           reinterpret_cast<uintptr_t>(MD));
  }

  static VTableComponent MakeCompleteDtor(const CXXDestructorDecl *DD) {
    return VTableComponent(CK_CompleteDtorPointer,
                           reinterpret_cast<uintptr_t>(DD));
  }

  static VTableComponent MakeDeletingDtor(const CXXDestructorDecl *DD) {
    return VTableComponent(CK_DeletingDtorPointer,
                           reinterpret_cast<uintptr_t>(DD));
  }

  static VTableComponent MakeUnusedFunction(const CXXMethodDecl *MD) {
    assert(!isa<CXXDestructorDecl>(MD) &&
           "Don't use MakeUnusedFunction with destructors!");
    return VTableComponent(CK_UnusedFunctionPointer,
                           reinterpret_cast<uintptr_t>(MD));
  }

  static VTableComponent getFromOpaqueInteger(uint64_t I) {
    return VTableComponent(I);
  }

  /// \brief Get the kind of this vtable component.
  Kind getKind() const {
    return (Kind)(Value & 0x7);
  }

  CharUnits getVCallOffset() const {
    assert(getKind() == CK_VCallOffset && "Invalid component kind!");

    return getOffset();
  }

  CharUnits getVBaseOffset() const {
    assert(getKind() == CK_VBaseOffset && "Invalid component kind!");

    return getOffset();
  }

  CharUnits getOffsetToTop() const {
    assert(getKind() == CK_OffsetToTop && "Invalid component kind!");

    return getOffset();
  }

  const CXXRecordDecl *getRTTIDecl() const {
    assert(isRTTIKind() && "Invalid component kind!");
    return reinterpret_cast<CXXRecordDecl *>(getPointer());
  }

  const CXXMethodDecl *getFunctionDecl() const {
    assert(isFunctionPointerKind() && "Invalid component kind!");
    if (isDestructorKind())
      return getDestructorDecl();
    return reinterpret_cast<CXXMethodDecl *>(getPointer());
  }

  const CXXDestructorDecl *getDestructorDecl() const {
    assert(isDestructorKind() && "Invalid component kind!");
    return reinterpret_cast<CXXDestructorDecl *>(getPointer());
  }

  const CXXMethodDecl *getUnusedFunctionDecl() const {
    assert(getKind() == CK_UnusedFunctionPointer && "Invalid component kind!");
    return reinterpret_cast<CXXMethodDecl *>(getPointer());
  }

  bool isDestructorKind() const { return isDestructorKind(getKind()); }

  bool isUsedFunctionPointerKind() const {
    return isUsedFunctionPointerKind(getKind());
  }

  bool isFunctionPointerKind() const {
    return isFunctionPointerKind(getKind());
  }

  bool isRTTIKind() const { return isRTTIKind(getKind()); }

private:
  static bool isFunctionPointerKind(Kind ComponentKind) {
    return isUsedFunctionPointerKind(ComponentKind) ||
           ComponentKind == CK_UnusedFunctionPointer;
  }
  static bool isUsedFunctionPointerKind(Kind ComponentKind) {
    return ComponentKind == CK_FunctionPointer ||
           isDestructorKind(ComponentKind);
  }
  static bool isDestructorKind(Kind ComponentKind) {
    return ComponentKind == CK_CompleteDtorPointer ||
           ComponentKind == CK_DeletingDtorPointer;
  }
  static bool isRTTIKind(Kind ComponentKind) {
    return ComponentKind == CK_RTTI;
  }

  VTableComponent(Kind ComponentKind, CharUnits Offset) {
    assert((ComponentKind == CK_VCallOffset ||
            ComponentKind == CK_VBaseOffset ||
            ComponentKind == CK_OffsetToTop) && "Invalid component kind!");
    assert(Offset.getQuantity() < (1LL << 56) && "Offset is too big!");
    assert(Offset.getQuantity() >= -(1LL << 56) && "Offset is too small!");

    Value = (uint64_t(Offset.getQuantity()) << 3) | ComponentKind;
  }

  VTableComponent(Kind ComponentKind, uintptr_t Ptr) {
    assert((isRTTIKind(ComponentKind) || isFunctionPointerKind(ComponentKind)) &&
           "Invalid component kind!");

    assert((Ptr & 7) == 0 && "Pointer not sufficiently aligned!");

    Value = Ptr | ComponentKind;
  }

  CharUnits getOffset() const {
    assert((getKind() == CK_VCallOffset || getKind() == CK_VBaseOffset ||
            getKind() == CK_OffsetToTop) && "Invalid component kind!");

    return CharUnits::fromQuantity(Value >> 3);
  }

  uintptr_t getPointer() const {
    assert((getKind() == CK_RTTI || isFunctionPointerKind()) &&
           "Invalid component kind!");

    return static_cast<uintptr_t>(Value & ~7ULL);
  }

  explicit VTableComponent(uint64_t Value)
    : Value(Value) { }

  /// The kind is stored in the lower 3 bits of the value. For offsets, we
  /// make use of the facts that classes can't be larger than 2^55 bytes,
  /// so we store the offset in the lower part of the 61 bits that remain.
  /// (The reason that we're not simply using a PointerIntPair here is that we
  /// need the offsets to be 64-bit, even when on a 32-bit machine).
  int64_t Value;
};

class VTableLayout {
public:
  typedef std::pair<uint64_t, ThunkInfo> VTableThunkTy;

  typedef const VTableComponent *vtable_component_iterator;
  typedef const VTableThunkTy *vtable_thunk_iterator;
  typedef llvm::iterator_range<vtable_component_iterator>
      vtable_component_range;

  typedef llvm::DenseMap<BaseSubobject, uint64_t> AddressPointsMapTy;

private:
  uint64_t NumVTableComponents;
  std::unique_ptr<VTableComponent[]> VTableComponents;

  /// \brief Contains thunks needed by vtables, sorted by indices.
  uint64_t NumVTableThunks;
  std::unique_ptr<VTableThunkTy[]> VTableThunks;

  /// \brief Address points for all vtables.
  AddressPointsMapTy AddressPoints;

  bool IsMicrosoftABI;

public:
  VTableLayout(uint64_t NumVTableComponents,
               const VTableComponent *VTableComponents,
               uint64_t NumVTableThunks,
               const VTableThunkTy *VTableThunks,
               const AddressPointsMapTy &AddressPoints,
               bool IsMicrosoftABI);
  ~VTableLayout();

  uint64_t getNumVTableComponents() const {
    return NumVTableComponents;
  }

  vtable_component_range vtable_components() const {
    return vtable_component_range(vtable_component_begin(),
                                  vtable_component_end());
  }

  vtable_component_iterator vtable_component_begin() const {
    return VTableComponents.get();
  }

  vtable_component_iterator vtable_component_end() const {
    return VTableComponents.get() + NumVTableComponents;
  }

  uint64_t getNumVTableThunks() const { return NumVTableThunks; }

  vtable_thunk_iterator vtable_thunk_begin() const {
    return VTableThunks.get();
  }

  vtable_thunk_iterator vtable_thunk_end() const {
    return VTableThunks.get() + NumVTableThunks;
  }

  uint64_t getAddressPoint(BaseSubobject Base) const {
    assert(AddressPoints.count(Base) &&
           "Did not find address point!");

    uint64_t AddressPoint = AddressPoints.lookup(Base);
    assert(AddressPoint != 0 || IsMicrosoftABI);
    (void)IsMicrosoftABI;

    return AddressPoint;
  }

  const AddressPointsMapTy &getAddressPoints() const {
    return AddressPoints;
  }
};

class VTableContextBase {
public:
  typedef SmallVector<ThunkInfo, 1> ThunkInfoVectorTy;

  bool isMicrosoft() const { return IsMicrosoftABI; }

  virtual ~VTableContextBase() {}

protected:
  typedef llvm::DenseMap<const CXXMethodDecl *, ThunkInfoVectorTy> ThunksMapTy;

  /// \brief Contains all thunks that a given method decl will need.
  ThunksMapTy Thunks;

  /// Compute and store all vtable related information (vtable layout, vbase
  /// offset offsets, thunks etc) for the given record decl.
  virtual void computeVTableRelatedInformation(const CXXRecordDecl *RD) = 0;

  VTableContextBase(bool MS) : IsMicrosoftABI(MS) {}

public:
  virtual const ThunkInfoVectorTy *getThunkInfo(GlobalDecl GD) {
    const CXXMethodDecl *MD = cast<CXXMethodDecl>(GD.getDecl()->getCanonicalDecl());
    computeVTableRelatedInformation(MD->getParent());

    // This assumes that all the destructors present in the vtable
    // use exactly the same set of thunks.
    ThunksMapTy::const_iterator I = Thunks.find(MD);
    if (I == Thunks.end()) {
      // We did not find a thunk for this method.
      return nullptr;
    }

    return &I->second;
  }

  bool IsMicrosoftABI;
};

class ItaniumVTableContext : public VTableContextBase {
private:

  /// \brief Contains the index (relative to the vtable address point)
  /// where the function pointer for a virtual function is stored.
  typedef llvm::DenseMap<GlobalDecl, int64_t> MethodVTableIndicesTy;
  MethodVTableIndicesTy MethodVTableIndices;

  typedef llvm::DenseMap<const CXXRecordDecl *, const VTableLayout *>
    VTableLayoutMapTy;
  VTableLayoutMapTy VTableLayouts;

  typedef std::pair<const CXXRecordDecl *,
                    const CXXRecordDecl *> ClassPairTy;

  /// \brief vtable offsets for offsets of virtual bases of a class.
  ///
  /// Contains the vtable offset (relative to the address point) in chars
  /// where the offsets for virtual bases of a class are stored.
  typedef llvm::DenseMap<ClassPairTy, CharUnits>
    VirtualBaseClassOffsetOffsetsMapTy;
  VirtualBaseClassOffsetOffsetsMapTy VirtualBaseClassOffsetOffsets;

  void computeVTableRelatedInformation(const CXXRecordDecl *RD) override;

public:
  ItaniumVTableContext(ASTContext &Context);
  ~ItaniumVTableContext() override;

  const VTableLayout &getVTableLayout(const CXXRecordDecl *RD) {
    computeVTableRelatedInformation(RD);
    assert(VTableLayouts.count(RD) && "No layout for this record decl!");

    return *VTableLayouts[RD];
  }

  VTableLayout *
  createConstructionVTableLayout(const CXXRecordDecl *MostDerivedClass,
                                 CharUnits MostDerivedClassOffset,
                                 bool MostDerivedClassIsVirtual,
                                 const CXXRecordDecl *LayoutClass);

  /// \brief Locate a virtual function in the vtable.
  ///
  /// Return the index (relative to the vtable address point) where the
  /// function pointer for the given virtual function is stored.
  uint64_t getMethodVTableIndex(GlobalDecl GD);

  /// Return the offset in chars (relative to the vtable address point) where
  /// the offset of the virtual base that contains the given base is stored,
  /// otherwise, if no virtual base contains the given class, return 0. 
  ///
  /// Base must be a virtual base class or an unambiguous base.
  CharUnits getVirtualBaseOffsetOffset(const CXXRecordDecl *RD,
                                       const CXXRecordDecl *VBase);

  static bool classof(const VTableContextBase *VT) {
    return !VT->isMicrosoft();
  }
};

/// Holds information about the inheritance path to a virtual base or function
/// table pointer.  A record may contain as many vfptrs or vbptrs as there are
/// base subobjects.
struct VPtrInfo {
  typedef SmallVector<const CXXRecordDecl *, 1> BasePath;

  VPtrInfo(const CXXRecordDecl *RD)
      : ReusingBase(RD), BaseWithVPtr(RD), NextBaseToMangle(RD) {}

  /// The vtable will hold all of the virtual bases or virtual methods of
  /// ReusingBase.  This may or may not be the same class as VPtrSubobject.Base.
  /// A derived class will reuse the vptr of the first non-virtual base
  /// subobject that has one.
  const CXXRecordDecl *ReusingBase;

  /// BaseWithVPtr is at this offset from its containing complete object or
  /// virtual base.
  CharUnits NonVirtualOffset;

  /// The vptr is stored inside this subobject.
  const CXXRecordDecl *BaseWithVPtr;

  /// The bases from the inheritance path that got used to mangle the vbtable
  /// name.  This is not really a full path like a CXXBasePath.  It holds the
  /// subset of records that need to be mangled into the vbtable symbol name in
  /// order to get a unique name.
  BasePath MangledPath;

  /// The next base to push onto the mangled path if this path is ambiguous in a
  /// derived class.  If it's null, then it's already been pushed onto the path.
  const CXXRecordDecl *NextBaseToMangle;

  /// The set of possibly indirect vbases that contain this vbtable.  When a
  /// derived class indirectly inherits from the same vbase twice, we only keep
  /// vtables and their paths from the first instance.
  BasePath ContainingVBases;

  /// This holds the base classes path from the complete type to the first base
  /// with the given vfptr offset, in the base-to-derived order.  Only used for
  /// vftables.
  BasePath PathToBaseWithVPtr;

  /// Static offset from the top of the most derived class to this vfptr,
  /// including any virtual base offset.  Only used for vftables.
  CharUnits FullOffsetInMDC;

  /// The vptr is stored inside the non-virtual component of this virtual base.
  const CXXRecordDecl *getVBaseWithVPtr() const {
    return ContainingVBases.empty() ? nullptr : ContainingVBases.front();
  }
};

typedef SmallVector<VPtrInfo *, 2> VPtrInfoVector;

/// All virtual base related information about a given record decl.  Includes
/// information on all virtual base tables and the path components that are used
/// to mangle them.
struct VirtualBaseInfo {
  ~VirtualBaseInfo() { llvm::DeleteContainerPointers(VBPtrPaths); }

  /// A map from virtual base to vbtable index for doing a conversion from the
  /// the derived class to the a base.
  llvm::DenseMap<const CXXRecordDecl *, unsigned> VBTableIndices;

  /// Information on all virtual base tables used when this record is the most
  /// derived class.
  VPtrInfoVector VBPtrPaths;
};

class MicrosoftVTableContext : public VTableContextBase {
public:
  struct MethodVFTableLocation {
    /// If nonzero, holds the vbtable index of the virtual base with the vfptr.
    uint64_t VBTableIndex;

    /// If nonnull, holds the last vbase which contains the vfptr that the
    /// method definition is adjusted to.
    const CXXRecordDecl *VBase;

    /// This is the offset of the vfptr from the start of the last vbase, or the
    /// complete type if there are no virtual bases.
    CharUnits VFPtrOffset;

    /// Method's index in the vftable.
    uint64_t Index;

    MethodVFTableLocation()
        : VBTableIndex(0), VBase(nullptr), VFPtrOffset(CharUnits::Zero()),
          Index(0) {}

    MethodVFTableLocation(uint64_t VBTableIndex, const CXXRecordDecl *VBase,
                          CharUnits VFPtrOffset, uint64_t Index)
        : VBTableIndex(VBTableIndex), VBase(VBase),
          VFPtrOffset(VFPtrOffset), Index(Index) {}

    bool operator<(const MethodVFTableLocation &other) const {
      if (VBTableIndex != other.VBTableIndex) {
        assert(VBase != other.VBase);
        return VBTableIndex < other.VBTableIndex;
      }
      return std::tie(VFPtrOffset, Index) <
             std::tie(other.VFPtrOffset, other.Index);
    }
  };

private:
  ASTContext &Context;

  typedef llvm::DenseMap<GlobalDecl, MethodVFTableLocation>
    MethodVFTableLocationsTy;
  MethodVFTableLocationsTy MethodVFTableLocations;

  typedef llvm::DenseMap<const CXXRecordDecl *, VPtrInfoVector *>
    VFPtrLocationsMapTy;
  VFPtrLocationsMapTy VFPtrLocations;

  typedef std::pair<const CXXRecordDecl *, CharUnits> VFTableIdTy;
  typedef llvm::DenseMap<VFTableIdTy, const VTableLayout *> VFTableLayoutMapTy;
  VFTableLayoutMapTy VFTableLayouts;

  llvm::DenseMap<const CXXRecordDecl *, VirtualBaseInfo *> VBaseInfo;

  void enumerateVFPtrs(const CXXRecordDecl *ForClass, VPtrInfoVector &Result);

  void computeVTableRelatedInformation(const CXXRecordDecl *RD) override;

  void dumpMethodLocations(const CXXRecordDecl *RD,
                           const MethodVFTableLocationsTy &NewMethods,
                           raw_ostream &);

  const VirtualBaseInfo *
  computeVBTableRelatedInformation(const CXXRecordDecl *RD);

  void computeVTablePaths(bool ForVBTables, const CXXRecordDecl *RD,
                          VPtrInfoVector &Paths);

public:
  MicrosoftVTableContext(ASTContext &Context)
      : VTableContextBase(/*MS=*/true), Context(Context) {}

  ~MicrosoftVTableContext() override;

  const VPtrInfoVector &getVFPtrOffsets(const CXXRecordDecl *RD);

  const VTableLayout &getVFTableLayout(const CXXRecordDecl *RD,
                                       CharUnits VFPtrOffset);

  const MethodVFTableLocation &getMethodVFTableLocation(GlobalDecl GD);

  const ThunkInfoVectorTy *getThunkInfo(GlobalDecl GD) override {
    // Complete destructors don't have a slot in a vftable, so no thunks needed.
    if (isa<CXXDestructorDecl>(GD.getDecl()) &&
        GD.getDtorType() == Dtor_Complete)
      return nullptr;
    return VTableContextBase::getThunkInfo(GD);
  }

  /// \brief Returns the index of VBase in the vbtable of Derived.
  /// VBase must be a morally virtual base of Derived.
  /// The vbtable is an array of i32 offsets.  The first entry is a self entry,
  /// and the rest are offsets from the vbptr to virtual bases.
  unsigned getVBTableIndex(const CXXRecordDecl *Derived,
                           const CXXRecordDecl *VBase);

  const VPtrInfoVector &enumerateVBTables(const CXXRecordDecl *RD);

  static bool classof(const VTableContextBase *VT) { return VT->isMicrosoft(); }
};

// Exposed for CALYPSO

/// BaseOffset - Represents an offset from a derived class to a direct or
/// indirect base class.
struct BaseOffset {
  /// DerivedClass - The derived class.
  const CXXRecordDecl *DerivedClass;

  /// VirtualBase - If the path from the derived class to the base class
  /// involves virtual base classes, this holds the declaration of the last
  /// virtual base in this path (i.e. closest to the base class).
  const CXXRecordDecl *VirtualBase;

  /// NonVirtualOffset - The offset from the derived class to the base class.
  /// (Or the offset from the virtual base class to the base class, if the
  /// path from the derived class to the base class involves a virtual base
  /// class.
  CharUnits NonVirtualOffset;

  BaseOffset() : DerivedClass(nullptr), VirtualBase(nullptr),
                 NonVirtualOffset(CharUnits::Zero()) { }
  BaseOffset(const CXXRecordDecl *DerivedClass,
             const CXXRecordDecl *VirtualBase, CharUnits NonVirtualOffset)
    : DerivedClass(DerivedClass), VirtualBase(VirtualBase),
    NonVirtualOffset(NonVirtualOffset) { }

  bool isEmpty() const { return NonVirtualOffset.isZero() && !VirtualBase; }
};

/// FinalOverriders - Contains the final overrider member functions for all
/// member functions in the base subobjects of a class.
class FinalOverriders {
public:
  /// OverriderInfo - Information about a final overrider.
  struct OverriderInfo {
    /// Method - The method decl of the overrider.
    const CXXMethodDecl *Method;

    /// VirtualBase - The virtual base class subobject of this overrider.
    /// Note that this records the closest derived virtual base class subobject.
    const CXXRecordDecl *VirtualBase;

    /// Offset - the base offset of the overrider's parent in the layout class.
    CharUnits Offset;

    OverriderInfo() : Method(nullptr), VirtualBase(nullptr),
                      Offset(CharUnits::Zero()) { }
  };

private:
  /// MostDerivedClass - The most derived class for which the final overriders
  /// are stored.
  const CXXRecordDecl *MostDerivedClass;

  /// MostDerivedClassOffset - If we're building final overriders for a
  /// construction vtable, this holds the offset from the layout class to the
  /// most derived class.
  const CharUnits MostDerivedClassOffset;

  /// LayoutClass - The class we're using for layout information. Will be
  /// different than the most derived class if the final overriders are for a
  /// construction vtable.
  const CXXRecordDecl *LayoutClass;

  ASTContext &Context;

  /// MostDerivedClassLayout - the AST record layout of the most derived class.
  const ASTRecordLayout &MostDerivedClassLayout;

  /// MethodBaseOffsetPairTy - Uniquely identifies a member function
  /// in a base subobject.
  typedef std::pair<const CXXMethodDecl *, CharUnits> MethodBaseOffsetPairTy;

  typedef llvm::DenseMap<MethodBaseOffsetPairTy,
                         OverriderInfo> OverridersMapTy;

  /// OverridersMap - The final overriders for all virtual member functions of
  /// all the base subobjects of the most derived class.
  OverridersMapTy OverridersMap;

  /// SubobjectsToOffsetsMapTy - A mapping from a base subobject (represented
  /// as a record decl and a subobject number) and its offsets in the most
  /// derived class as well as the layout class.
  typedef llvm::DenseMap<std::pair<const CXXRecordDecl *, unsigned>,
                         CharUnits> SubobjectOffsetMapTy;

  typedef llvm::DenseMap<const CXXRecordDecl *, unsigned> SubobjectCountMapTy;

  /// ComputeBaseOffsets - Compute the offsets for all base subobjects of the
  /// given base.
  void ComputeBaseOffsets(BaseSubobject Base, bool IsVirtual,
                          CharUnits OffsetInLayoutClass,
                          SubobjectOffsetMapTy &SubobjectOffsets,
                          SubobjectOffsetMapTy &SubobjectLayoutClassOffsets,
                          SubobjectCountMapTy &SubobjectCounts);

  typedef llvm::SmallPtrSet<const CXXRecordDecl *, 4> VisitedVirtualBasesSetTy;

  /// dump - dump the final overriders for a base subobject, and all its direct
  /// and indirect base subobjects.
  void dump(raw_ostream &Out, BaseSubobject Base,
            VisitedVirtualBasesSetTy& VisitedVirtualBases);

public:
  FinalOverriders(const CXXRecordDecl *MostDerivedClass,
                  CharUnits MostDerivedClassOffset,
                  const CXXRecordDecl *LayoutClass);

  /// getOverrider - Get the final overrider for the given method declaration in
  /// the subobject with the given base offset.
  OverriderInfo getOverrider(const CXXMethodDecl *MD,
                             CharUnits BaseOffset) const {
    assert(OverridersMap.count(std::make_pair(MD, BaseOffset)) &&
           "Did not find overrider!");

    return OverridersMap.lookup(std::make_pair(MD, BaseOffset));
  }

  /// dump - dump the final overriders.
  void dump() {
    VisitedVirtualBasesSetTy VisitedVirtualBases;
    dump(llvm::errs(), BaseSubobject(MostDerivedClass, CharUnits::Zero()),
         VisitedVirtualBases);
  }

};

/// VCallOffsetMap - Keeps track of vcall offsets when building a vtable.
struct VCallOffsetMap {

  typedef std::pair<const CXXMethodDecl *, CharUnits> MethodAndOffsetPairTy;

  /// Offsets - Keeps track of methods and their offsets.
  // FIXME: This should be a real map and not a vector.
  SmallVector<MethodAndOffsetPairTy, 16> Offsets;

  /// MethodsCanShareVCallOffset - Returns whether two virtual member functions
  /// can share the same vcall offset.
  static bool MethodsCanShareVCallOffset(const CXXMethodDecl *LHS,
                                         const CXXMethodDecl *RHS);

public:
  /// AddVCallOffset - Adds a vcall offset to the map. Returns true if the
  /// add was successful, or false if there was already a member function with
  /// the same signature in the map.
  bool AddVCallOffset(const CXXMethodDecl *MD, CharUnits OffsetOffset);

  /// getVCallOffsetOffset - Returns the vcall offset offset (relative to the
  /// vtable address point) for the given virtual member function.
  CharUnits getVCallOffsetOffset(const CXXMethodDecl *MD);

  // empty - Return whether the offset map is empty or not.
  bool empty() const { return Offsets.empty(); }
};

/// ItaniumVTableBuilder - Class for building vtable layout information.
class ItaniumVTableBuilder {
public:
  /// PrimaryBasesSetVectorTy - A set vector of direct and indirect
  /// primary bases.
  typedef llvm::SmallSetVector<const CXXRecordDecl *, 8>
    PrimaryBasesSetVectorTy;

  typedef llvm::DenseMap<const CXXRecordDecl *, CharUnits>
    VBaseOffsetOffsetsMapTy;

  typedef llvm::DenseMap<BaseSubobject, uint64_t>
    AddressPointsMapTy;

  typedef llvm::DenseMap<GlobalDecl, int64_t> MethodVTableIndicesTy;

// private: // CALYPSO
  /// VTables - Global vtable information.
  ItaniumVTableContext &VTables;

  /// MostDerivedClass - The most derived class for which we're building this
  /// vtable.
  const CXXRecordDecl *MostDerivedClass;

  /// MostDerivedClassOffset - If we're building a construction vtable, this
  /// holds the offset from the layout class to the most derived class.
  const CharUnits MostDerivedClassOffset;

  /// MostDerivedClassIsVirtual - Whether the most derived class is a virtual
  /// base. (This only makes sense when building a construction vtable).
  bool MostDerivedClassIsVirtual;

  /// LayoutClass - The class we're using for layout information. Will be
  /// different than the most derived class if we're building a construction
  /// vtable.
  const CXXRecordDecl *LayoutClass;

  /// Context - The ASTContext which we will use for layout information.
  ASTContext &Context;

  /// FinalOverriders - The final overriders of the most derived class.
  const FinalOverriders Overriders;

  /// VCallOffsetsForVBases - Keeps track of vcall offsets for the virtual
  /// bases in this vtable.
  llvm::DenseMap<const CXXRecordDecl *, VCallOffsetMap> VCallOffsetsForVBases;

  /// VBaseOffsetOffsets - Contains the offsets of the virtual base offsets for
  /// the most derived class.
  VBaseOffsetOffsetsMapTy VBaseOffsetOffsets;

  /// Components - The components of the vtable being built.
  SmallVector<VTableComponent, 64> Components;

  /// AddressPoints - Address points for the vtable being built.
  AddressPointsMapTy AddressPoints;

  /// MethodInfo - Contains information about a method in a vtable.
  /// (Used for computing 'this' pointer adjustment thunks.
  struct MethodInfo {
    /// BaseOffset - The base offset of this method.
    const CharUnits BaseOffset;

    /// BaseOffsetInLayoutClass - The base offset in the layout class of this
    /// method.
    const CharUnits BaseOffsetInLayoutClass;

    /// VTableIndex - The index in the vtable that this method has.
    /// (For destructors, this is the index of the complete destructor).
    const uint64_t VTableIndex;

    MethodInfo(CharUnits BaseOffset, CharUnits BaseOffsetInLayoutClass,
               uint64_t VTableIndex)
      : BaseOffset(BaseOffset),
      BaseOffsetInLayoutClass(BaseOffsetInLayoutClass),
      VTableIndex(VTableIndex) { }

    MethodInfo()
      : BaseOffset(CharUnits::Zero()),
      BaseOffsetInLayoutClass(CharUnits::Zero()),
      VTableIndex(0) { }
  };

  typedef llvm::DenseMap<const CXXMethodDecl *, MethodInfo> MethodInfoMapTy;

  /// MethodInfoMap - The information for all methods in the vtable we're
  /// currently building.
  MethodInfoMapTy MethodInfoMap;

  /// MethodVTableIndices - Contains the index (relative to the vtable address
  /// point) where the function pointer for a virtual function is stored.
  MethodVTableIndicesTy MethodVTableIndices;

  typedef llvm::DenseMap<uint64_t, ThunkInfo> VTableThunksMapTy;

  /// VTableThunks - The thunks by vtable index in the vtable currently being
  /// built.
  VTableThunksMapTy VTableThunks;

  typedef SmallVector<ThunkInfo, 1> ThunkInfoVectorTy;
  typedef llvm::DenseMap<const CXXMethodDecl *, ThunkInfoVectorTy> ThunksMapTy;

  /// Thunks - A map that contains all the thunks needed for all methods in the
  /// most derived class for which the vtable is currently being built.
  ThunksMapTy Thunks;

  /// AddThunk - Add a thunk for the given method.
  void AddThunk(const CXXMethodDecl *MD, const ThunkInfo &Thunk);

  /// ComputeThisAdjustments - Compute the 'this' pointer adjustments for the
  /// part of the vtable we're currently building.
  void ComputeThisAdjustments();

  typedef llvm::SmallPtrSet<const CXXRecordDecl *, 4> VisitedVirtualBasesSetTy;

  /// PrimaryVirtualBases - All known virtual bases who are a primary base of
  /// some other base.
  VisitedVirtualBasesSetTy PrimaryVirtualBases;

  /// ComputeReturnAdjustment - Compute the return adjustment given a return
  /// adjustment base offset.
  ReturnAdjustment ComputeReturnAdjustment(BaseOffset Offset);

  /// ComputeThisAdjustmentBaseOffset - Compute the base offset for adjusting
  /// the 'this' pointer from the base subobject to the derived subobject.
  BaseOffset ComputeThisAdjustmentBaseOffset(BaseSubobject Base,
                                             BaseSubobject Derived) const;

  /// ComputeThisAdjustment - Compute the 'this' pointer adjustment for the
  /// given virtual member function, its offset in the layout class and its
  /// final overrider.
  ThisAdjustment
  ComputeThisAdjustment(const CXXMethodDecl *MD,
                        CharUnits BaseOffsetInLayoutClass,
                        FinalOverriders::OverriderInfo Overrider);

  /// AddMethod - Add a single virtual member function to the vtable
  /// components vector.
  void AddMethod(const CXXMethodDecl *MD, ReturnAdjustment ReturnAdjustment);

  /// IsOverriderUsed - Returns whether the overrider will ever be used in this
  /// part of the vtable.
  ///
  /// Itanium C++ ABI 2.5.2:
  ///
  ///   struct A { virtual void f(); };
  ///   struct B : virtual public A { int i; };
  ///   struct C : virtual public A { int j; };
  ///   struct D : public B, public C {};
  ///
  ///   When B and C are declared, A is a primary base in each case, so although
  ///   vcall offsets are allocated in the A-in-B and A-in-C vtables, no this
  ///   adjustment is required and no thunk is generated. However, inside D
  ///   objects, A is no longer a primary base of C, so if we allowed calls to
  ///   C::f() to use the copy of A's vtable in the C subobject, we would need
  ///   to adjust this from C* to B::A*, which would require a third-party
  ///   thunk. Since we require that a call to C::f() first convert to A*,
  ///   C-in-D's copy of A's vtable is never referenced, so this is not
  ///   necessary.
  bool IsOverriderUsed(const CXXMethodDecl *Overrider,
                       CharUnits BaseOffsetInLayoutClass,
                       const CXXRecordDecl *FirstBaseInPrimaryBaseChain,
                       CharUnits FirstBaseOffsetInLayoutClass) const;


  /// AddMethods - Add the methods of this base subobject and all its
  /// primary bases to the vtable components vector.
  void AddMethods(BaseSubobject Base, CharUnits BaseOffsetInLayoutClass,
                  const CXXRecordDecl *FirstBaseInPrimaryBaseChain,
                  CharUnits FirstBaseOffsetInLayoutClass,
                  PrimaryBasesSetVectorTy &PrimaryBases);

  // LayoutVTable - Layout the vtable for the given base class, including its
  // secondary vtables and any vtables for virtual bases.
  void LayoutVTable();

  /// LayoutPrimaryAndSecondaryVTables - Layout the primary vtable for the
  /// given base subobject, as well as all its secondary vtables.
  ///
  /// \param BaseIsMorallyVirtual whether the base subobject is a virtual base
  /// or a direct or indirect base of a virtual base.
  ///
  /// \param BaseIsVirtualInLayoutClass - Whether the base subobject is virtual
  /// in the layout class.
  void LayoutPrimaryAndSecondaryVTables(BaseSubobject Base,
                                        bool BaseIsMorallyVirtual,
                                        bool BaseIsVirtualInLayoutClass,
                                        CharUnits OffsetInLayoutClass);

  /// LayoutSecondaryVTables - Layout the secondary vtables for the given base
  /// subobject.
  ///
  /// \param BaseIsMorallyVirtual whether the base subobject is a virtual base
  /// or a direct or indirect base of a virtual base.
  void LayoutSecondaryVTables(BaseSubobject Base, bool BaseIsMorallyVirtual,
                              CharUnits OffsetInLayoutClass);

  /// DeterminePrimaryVirtualBases - Determine the primary virtual bases in this
  /// class hierarchy.
  void DeterminePrimaryVirtualBases(const CXXRecordDecl *RD,
                                    CharUnits OffsetInLayoutClass,
                                    VisitedVirtualBasesSetTy &VBases);

  /// LayoutVTablesForVirtualBases - Layout vtables for all virtual bases of the
  /// given base (excluding any primary bases).
  void LayoutVTablesForVirtualBases(const CXXRecordDecl *RD,
                                    VisitedVirtualBasesSetTy &VBases);

  /// isBuildingConstructionVTable - Return whether this vtable builder is
  /// building a construction vtable.
  bool isBuildingConstructorVTable() const {
    return MostDerivedClass != LayoutClass;
  }

public:
  ItaniumVTableBuilder(ItaniumVTableContext &VTables,
                       const CXXRecordDecl *MostDerivedClass,
                       CharUnits MostDerivedClassOffset,
                       bool MostDerivedClassIsVirtual,
                       const CXXRecordDecl *LayoutClass);

  uint64_t getNumThunks() const {
    return Thunks.size();
  }

  ThunksMapTy::const_iterator thunks_begin() const {
    return Thunks.begin();
  }

  ThunksMapTy::const_iterator thunks_end() const {
    return Thunks.end();
  }

  const VBaseOffsetOffsetsMapTy &getVBaseOffsetOffsets() const {
    return VBaseOffsetOffsets;
  }

  const AddressPointsMapTy &getAddressPoints() const {
    return AddressPoints;
  }

  MethodVTableIndicesTy::const_iterator vtable_indices_begin() const {
    return MethodVTableIndices.begin();
  }

  MethodVTableIndicesTy::const_iterator vtable_indices_end() const {
    return MethodVTableIndices.end();
  }

  /// getNumVTableComponents - Return the number of components in the vtable
  /// currently built.
  uint64_t getNumVTableComponents() const {
    return Components.size();
  }

  const VTableComponent *vtable_component_begin() const {
    return Components.begin();
  }

  const VTableComponent *vtable_component_end() const {
    return Components.end();
  }

  AddressPointsMapTy::const_iterator address_points_begin() const {
    return AddressPoints.begin();
  }

  AddressPointsMapTy::const_iterator address_points_end() const {
    return AddressPoints.end();
  }

  VTableThunksMapTy::const_iterator vtable_thunks_begin() const {
    return VTableThunks.begin();
  }

  VTableThunksMapTy::const_iterator vtable_thunks_end() const {
    return VTableThunks.end();
  }

  /// dumpLayout - Dump the vtable layout.
  void dumpLayout(raw_ostream&);
};

// CALYPSO
BaseOffset ComputeBaseOffset(const ASTContext &Context,
                                    const CXXRecordDecl *BaseRD,
                                    const CXXRecordDecl *DerivedRD);

} // namespace clang

#endif
