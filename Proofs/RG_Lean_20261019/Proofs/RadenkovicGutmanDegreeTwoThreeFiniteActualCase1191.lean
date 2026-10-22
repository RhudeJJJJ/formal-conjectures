/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1191 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap1191 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 0 2 v)
def fusedMap1191 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1191_checked : acceptsGraphIso
    (source (graph core1191) (root 8) 0 2) DegreeOneSmallSpectrum1601.graph sourceMap1191=true := by decide +kernel
theorem fusedMap1191_checked : acceptsGraphIso
    (fused (graph core1191) (root 8) 0 2) DegreeOneSmallSpectrum1604.graph fusedMap1191=true := by decide +kernel
theorem certified1191 : Certified (graph core1191) (root 8) 0 2 :=
  of_native_maps core1191 DegreeOneSmallSpectrum1601.graph DegreeOneSmallSpectrum1604.graph
    sourceMap1191 fusedMap1191 sourceMap1191_checked fusedMap1191_checked
    DegreeTwoThreeFiniteComparisons.comparison1191
#print axioms sourceMap1191_checked
#print axioms fusedMap1191_checked
#print axioms certified1191
def sourceMap1191swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,9] (sourceLabel 8 2 0 v)
def fusedMap1191swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1191swap_checked : acceptsGraphIso
    (source (graph core1191) (root 8) 2 0) DegreeOneSmallSpectrum1601.graph sourceMap1191swap=true := by decide +kernel
theorem fusedMap1191swap_checked : acceptsGraphIso
    (fused (graph core1191) (root 8) 2 0) DegreeOneSmallSpectrum1604.graph fusedMap1191swap=true := by decide +kernel
theorem certified1191swap : Certified (graph core1191) (root 8) 2 0 :=
  of_native_maps core1191 DegreeOneSmallSpectrum1601.graph DegreeOneSmallSpectrum1604.graph
    sourceMap1191swap fusedMap1191swap sourceMap1191swap_checked fusedMap1191swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1191
#print axioms sourceMap1191swap_checked
#print axioms fusedMap1191swap_checked
#print axioms certified1191swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
