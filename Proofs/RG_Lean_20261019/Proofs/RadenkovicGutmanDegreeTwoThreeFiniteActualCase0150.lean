/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0150 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap0150 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0150 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0150_checked : acceptsGraphIso
    (source (graph core0150) (root 8) 0 0) SmallGeFourSpectrum063.graph sourceMap0150=true := by decide +kernel
theorem fusedMap0150_checked : acceptsGraphIso
    (fused (graph core0150) (root 8) 0 0) SmallGeFourSpectrum059.graph fusedMap0150=true := by decide +kernel
theorem certified0150 : Certified (graph core0150) (root 8) 0 0 :=
  of_native_maps core0150 SmallGeFourSpectrum063.graph SmallGeFourSpectrum059.graph
    sourceMap0150 fusedMap0150 sourceMap0150_checked fusedMap0150_checked
    DegreeTwoThreeFiniteComparisons.comparison0150
#print axioms sourceMap0150_checked
#print axioms fusedMap0150_checked
#print axioms certified0150
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
