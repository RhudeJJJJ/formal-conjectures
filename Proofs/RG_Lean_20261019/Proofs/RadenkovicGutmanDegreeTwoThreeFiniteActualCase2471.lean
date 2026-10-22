/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2471 : Family 10 := level10.get ⟨98,by decide⟩
def sourceMap2471 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2471 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2471_checked : acceptsGraphIso
    (source (graph core2471) (root 10) 0 4) DegreeTwoThreeSpectrum5537.graph sourceMap2471=true := by decide +kernel
theorem fusedMap2471_checked : acceptsGraphIso
    (fused (graph core2471) (root 10) 0 4) DegreeTwoThreeSpectrum5019.graph fusedMap2471=true := by decide +kernel
theorem certified2471 : Certified (graph core2471) (root 10) 0 4 :=
  of_native_maps core2471 DegreeTwoThreeSpectrum5537.graph DegreeTwoThreeSpectrum5019.graph
    sourceMap2471 fusedMap2471 sourceMap2471_checked fusedMap2471_checked
    DegreeTwoThreeFiniteComparisons.comparison2471
#print axioms sourceMap2471_checked
#print axioms fusedMap2471_checked
#print axioms certified2471
def sourceMap2471swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2471swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2471swap_checked : acceptsGraphIso
    (source (graph core2471) (root 10) 4 0) DegreeTwoThreeSpectrum5537.graph sourceMap2471swap=true := by decide +kernel
theorem fusedMap2471swap_checked : acceptsGraphIso
    (fused (graph core2471) (root 10) 4 0) DegreeTwoThreeSpectrum5019.graph fusedMap2471swap=true := by decide +kernel
theorem certified2471swap : Certified (graph core2471) (root 10) 4 0 :=
  of_native_maps core2471 DegreeTwoThreeSpectrum5537.graph DegreeTwoThreeSpectrum5019.graph
    sourceMap2471swap fusedMap2471swap sourceMap2471swap_checked fusedMap2471swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2471
#print axioms sourceMap2471swap_checked
#print axioms fusedMap2471swap_checked
#print axioms certified2471swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
