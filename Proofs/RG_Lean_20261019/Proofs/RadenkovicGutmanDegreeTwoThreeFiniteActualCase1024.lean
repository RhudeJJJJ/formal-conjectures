/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1024 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap1024 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,6,7,4,5] (sourceLabel 4 0 1 v)
def fusedMap1024 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 0 1 v)
theorem sourceMap1024_checked : acceptsGraphIso
    (source (graph core1024) (root 4) 0 1) DegreeOneSmallSpectrum033.graph sourceMap1024=true := by decide +kernel
theorem fusedMap1024_checked : acceptsGraphIso
    (fused (graph core1024) (root 4) 0 1) DegreeOneSmallSpectrum018.graph fusedMap1024=true := by decide +kernel
theorem certified1024 : Certified (graph core1024) (root 4) 0 1 :=
  of_native_maps core1024 DegreeOneSmallSpectrum033.graph DegreeOneSmallSpectrum018.graph
    sourceMap1024 fusedMap1024 sourceMap1024_checked fusedMap1024_checked
    DegreeTwoThreeFiniteComparisons.comparison1024
#print axioms sourceMap1024_checked
#print axioms fusedMap1024_checked
#print axioms certified1024
def sourceMap1024swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,6,4,5,7] (sourceLabel 4 1 0 v)
def fusedMap1024swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 1 0 v)
theorem sourceMap1024swap_checked : acceptsGraphIso
    (source (graph core1024) (root 4) 1 0) DegreeOneSmallSpectrum033.graph sourceMap1024swap=true := by decide +kernel
theorem fusedMap1024swap_checked : acceptsGraphIso
    (fused (graph core1024) (root 4) 1 0) DegreeOneSmallSpectrum018.graph fusedMap1024swap=true := by decide +kernel
theorem certified1024swap : Certified (graph core1024) (root 4) 1 0 :=
  of_native_maps core1024 DegreeOneSmallSpectrum033.graph DegreeOneSmallSpectrum018.graph
    sourceMap1024swap fusedMap1024swap sourceMap1024swap_checked fusedMap1024swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1024
#print axioms sourceMap1024swap_checked
#print axioms fusedMap1024swap_checked
#print axioms certified1024swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
