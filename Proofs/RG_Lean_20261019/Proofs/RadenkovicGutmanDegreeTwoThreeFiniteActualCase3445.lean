/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3445 : Family 9 := level9.get ⟨601,by decide⟩
def sourceMap3445 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3445 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3445_checked : acceptsGraphIso
    (source (graph core3445) (root 9) 0 5) DegreeTwoThreeSpectrum6239.graph sourceMap3445=true := by decide +kernel
theorem fusedMap3445_checked : acceptsGraphIso
    (fused (graph core3445) (root 9) 0 5) DegreeTwoThreeSpectrum6240.graph fusedMap3445=true := by decide +kernel
theorem certified3445 : Certified (graph core3445) (root 9) 0 5 :=
  of_native_maps core3445 DegreeTwoThreeSpectrum6239.graph DegreeTwoThreeSpectrum6240.graph
    sourceMap3445 fusedMap3445 sourceMap3445_checked fusedMap3445_checked
    DegreeTwoThreeFiniteComparisons.comparison3445
#print axioms sourceMap3445_checked
#print axioms fusedMap3445_checked
#print axioms certified3445
def sourceMap3445swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3445swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3445swap_checked : acceptsGraphIso
    (source (graph core3445) (root 9) 5 0) DegreeTwoThreeSpectrum6239.graph sourceMap3445swap=true := by decide +kernel
theorem fusedMap3445swap_checked : acceptsGraphIso
    (fused (graph core3445) (root 9) 5 0) DegreeTwoThreeSpectrum6240.graph fusedMap3445swap=true := by decide +kernel
theorem certified3445swap : Certified (graph core3445) (root 9) 5 0 :=
  of_native_maps core3445 DegreeTwoThreeSpectrum6239.graph DegreeTwoThreeSpectrum6240.graph
    sourceMap3445swap fusedMap3445swap sourceMap3445swap_checked fusedMap3445swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3445
#print axioms sourceMap3445swap_checked
#print axioms fusedMap3445swap_checked
#print axioms certified3445swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
