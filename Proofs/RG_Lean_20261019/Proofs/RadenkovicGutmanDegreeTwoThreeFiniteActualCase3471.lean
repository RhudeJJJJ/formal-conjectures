/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3471 : Family 9 := level9.get ⟨690,by decide⟩
def sourceMap3471 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3471 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3471_checked : acceptsGraphIso
    (source (graph core3471) (root 9) 0 5) DegreeTwoThreeSpectrum7061.graph sourceMap3471=true := by decide +kernel
theorem fusedMap3471_checked : acceptsGraphIso
    (fused (graph core3471) (root 9) 0 5) DegreeTwoThreeSpectrum5960.graph fusedMap3471=true := by decide +kernel
theorem certified3471 : Certified (graph core3471) (root 9) 0 5 :=
  of_native_maps core3471 DegreeTwoThreeSpectrum7061.graph DegreeTwoThreeSpectrum5960.graph
    sourceMap3471 fusedMap3471 sourceMap3471_checked fusedMap3471_checked
    DegreeTwoThreeFiniteComparisons.comparison3471
#print axioms sourceMap3471_checked
#print axioms fusedMap3471_checked
#print axioms certified3471
def sourceMap3471swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,13,14,15,16,12] (sourceLabel 9 5 0 v)
def fusedMap3471swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3471swap_checked : acceptsGraphIso
    (source (graph core3471) (root 9) 5 0) DegreeTwoThreeSpectrum7061.graph sourceMap3471swap=true := by decide +kernel
theorem fusedMap3471swap_checked : acceptsGraphIso
    (fused (graph core3471) (root 9) 5 0) DegreeTwoThreeSpectrum5960.graph fusedMap3471swap=true := by decide +kernel
theorem certified3471swap : Certified (graph core3471) (root 9) 5 0 :=
  of_native_maps core3471 DegreeTwoThreeSpectrum7061.graph DegreeTwoThreeSpectrum5960.graph
    sourceMap3471swap fusedMap3471swap sourceMap3471swap_checked fusedMap3471swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3471
#print axioms sourceMap3471swap_checked
#print axioms fusedMap3471swap_checked
#print axioms certified3471swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
