/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1830 : Family 10 := level10.get ⟨76,by decide⟩
def sourceMap1830 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1830 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1830_checked : acceptsGraphIso
    (source (graph core1830) (root 10) 0 0) DegreeOneSmallSpectrum1163.graph sourceMap1830=true := by decide +kernel
theorem fusedMap1830_checked : acceptsGraphIso
    (fused (graph core1830) (root 10) 0 0) DegreeOneSmallSpectrum892.graph fusedMap1830=true := by decide +kernel
theorem certified1830 : Certified (graph core1830) (root 10) 0 0 :=
  of_native_maps core1830 DegreeOneSmallSpectrum1163.graph DegreeOneSmallSpectrum892.graph
    sourceMap1830 fusedMap1830 sourceMap1830_checked fusedMap1830_checked
    DegreeOneSmallComparisons.comparison1830
#print axioms sourceMap1830_checked
#print axioms fusedMap1830_checked
#print axioms certified1830
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
