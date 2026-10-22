/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1043 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap1043 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 6 0 2 v)
def fusedMap1043 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,5,1,2,3,4] (fusedLabel 6 0 2 v)
theorem sourceMap1043_checked : acceptsGraphIso
    (source (graph core1043) (root 6) 0 2) DegreeOneSmallSpectrum225.graph sourceMap1043=true := by decide +kernel
theorem fusedMap1043_checked : acceptsGraphIso
    (fused (graph core1043) (root 6) 0 2) DegreeOneSmallSpectrum167.graph fusedMap1043=true := by decide +kernel
theorem certified1043 : Certified (graph core1043) (root 6) 0 2 :=
  of_native_maps core1043 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum167.graph
    sourceMap1043 fusedMap1043 sourceMap1043_checked fusedMap1043_checked
    DegreeTwoThreeFiniteComparisons.comparison1043
#print axioms sourceMap1043_checked
#print axioms fusedMap1043_checked
#print axioms certified1043
def sourceMap1043swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,2,3,4,6] (sourceLabel 6 2 0 v)
def fusedMap1043swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,5,1,2,3,4] (fusedLabel 6 2 0 v)
theorem sourceMap1043swap_checked : acceptsGraphIso
    (source (graph core1043) (root 6) 2 0) DegreeOneSmallSpectrum225.graph sourceMap1043swap=true := by decide +kernel
theorem fusedMap1043swap_checked : acceptsGraphIso
    (fused (graph core1043) (root 6) 2 0) DegreeOneSmallSpectrum167.graph fusedMap1043swap=true := by decide +kernel
theorem certified1043swap : Certified (graph core1043) (root 6) 2 0 :=
  of_native_maps core1043 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum167.graph
    sourceMap1043swap fusedMap1043swap sourceMap1043swap_checked fusedMap1043swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1043
#print axioms sourceMap1043swap_checked
#print axioms fusedMap1043swap_checked
#print axioms certified1043swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
