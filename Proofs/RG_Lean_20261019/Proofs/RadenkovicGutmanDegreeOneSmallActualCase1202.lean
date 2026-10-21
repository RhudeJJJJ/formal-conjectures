/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1202 : Family 9 := level9.get ⟨3,by decide⟩
def sourceMap1202 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 9 0 1 v)
def fusedMap1202 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1202_checked : acceptsGraphIso
    (source (graph core1202) (root 9) 0 1) DegreeOneSmallSpectrum940.graph sourceMap1202=true := by decide +kernel
theorem fusedMap1202_checked : acceptsGraphIso
    (fused (graph core1202) (root 9) 0 1) DegreeOneSmallSpectrum858.graph fusedMap1202=true := by decide +kernel
theorem certified1202 : Certified (graph core1202) (root 9) 0 1 :=
  of_native_maps core1202 DegreeOneSmallSpectrum940.graph DegreeOneSmallSpectrum858.graph
    sourceMap1202 fusedMap1202 sourceMap1202_checked fusedMap1202_checked
    DegreeOneSmallComparisons.comparison1202
#print axioms sourceMap1202_checked
#print axioms fusedMap1202_checked
#print axioms certified1202
def sourceMap1202swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 9 1 0 v)
def fusedMap1202swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1202swap_checked : acceptsGraphIso
    (source (graph core1202) (root 9) 1 0) DegreeOneSmallSpectrum940.graph sourceMap1202swap=true := by decide +kernel
theorem fusedMap1202swap_checked : acceptsGraphIso
    (fused (graph core1202) (root 9) 1 0) DegreeOneSmallSpectrum858.graph fusedMap1202swap=true := by decide +kernel
theorem certified1202swap : Certified (graph core1202) (root 9) 1 0 :=
  of_native_maps core1202 DegreeOneSmallSpectrum940.graph DegreeOneSmallSpectrum858.graph
    sourceMap1202swap fusedMap1202swap sourceMap1202swap_checked fusedMap1202swap_checked
    DegreeOneSmallComparisons.comparison1202
#print axioms sourceMap1202swap_checked
#print axioms fusedMap1202swap_checked
#print axioms certified1202swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
