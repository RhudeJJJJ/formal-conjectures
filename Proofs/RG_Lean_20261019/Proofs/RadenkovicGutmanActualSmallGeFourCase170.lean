/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core170 : Family 9 := level9.get ⟨136,by decide⟩
def sourceMap170 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap170 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap170_checked : acceptsGraphIso
    (source (graph core170) (root 9) 0 0) SmallGeFourSpectrum093.graph
      sourceMap170=true := by decide +kernel
theorem fusedMap170_checked : acceptsGraphIso
    (fused (graph core170) (root 9) 0 0) SmallGeFourSpectrum104.graph
      fusedMap170=true := by decide +kernel
theorem certified170 : Certified (graph core170) (root 9) 0 0 :=
  of_native_maps core170 SmallGeFourSpectrum093.graph SmallGeFourSpectrum104.graph
    sourceMap170 fusedMap170 sourceMap170_checked fusedMap170_checked
    SmallGeFourComparisons.comparison170
#print axioms sourceMap170_checked
#print axioms fusedMap170_checked
#print axioms certified170
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
