/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1725 : Family 9 := level9.get ⟨543,by decide⟩
def sourceMap1725 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1725 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1725_checked : acceptsGraphIso
    (source (graph core1725) (root 9) 0 0) SmallGeFourSpectrum205.graph sourceMap1725=true := by decide +kernel
theorem fusedMap1725_checked : acceptsGraphIso
    (fused (graph core1725) (root 9) 0 0) SmallGeFourSpectrum113.graph fusedMap1725=true := by decide +kernel
theorem certified1725 : Certified (graph core1725) (root 9) 0 0 :=
  of_native_maps core1725 SmallGeFourSpectrum205.graph SmallGeFourSpectrum113.graph
    sourceMap1725 fusedMap1725 sourceMap1725_checked fusedMap1725_checked
    DegreeOneSmallComparisons.comparison1725
#print axioms sourceMap1725_checked
#print axioms fusedMap1725_checked
#print axioms certified1725
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
