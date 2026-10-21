/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1854 : Family 10 := level10.get ⟨108,by decide⟩
def sourceMap1854 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1854 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1854_checked : acceptsGraphIso
    (source (graph core1854) (root 10) 0 0) DegreeOneSmallSpectrum1173.graph sourceMap1854=true := by decide +kernel
theorem fusedMap1854_checked : acceptsGraphIso
    (fused (graph core1854) (root 10) 0 0) DegreeOneSmallSpectrum933.graph fusedMap1854=true := by decide +kernel
theorem certified1854 : Certified (graph core1854) (root 10) 0 0 :=
  of_native_maps core1854 DegreeOneSmallSpectrum1173.graph DegreeOneSmallSpectrum933.graph
    sourceMap1854 fusedMap1854 sourceMap1854_checked fusedMap1854_checked
    DegreeOneSmallComparisons.comparison1854
#print axioms sourceMap1854_checked
#print axioms fusedMap1854_checked
#print axioms certified1854
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
