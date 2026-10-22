/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5214 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap5214 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,2,3,4,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5214 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5214_checked : acceptsGraphIso
    (source (graph core5214) (root 8) 2 4) DegreeTwoThreeSpectrum7556.graph sourceMap5214=true := by decide +kernel
theorem fusedMap5214_checked : acceptsGraphIso
    (fused (graph core5214) (root 8) 2 4) DegreeTwoThreeSpectrum6047.graph fusedMap5214=true := by decide +kernel
theorem certified5214 : Certified (graph core5214) (root 8) 2 4 :=
  of_native_maps core5214 DegreeTwoThreeSpectrum7556.graph DegreeTwoThreeSpectrum6047.graph
    sourceMap5214 fusedMap5214 sourceMap5214_checked fusedMap5214_checked
    DegreeTwoThreeFiniteComparisons.comparison5214
#print axioms sourceMap5214_checked
#print axioms fusedMap5214_checked
#print axioms certified5214
def sourceMap5214swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,0,13,14,15,16,2,3,4] (sourceLabel 8 4 2 v)
def fusedMap5214swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5214swap_checked : acceptsGraphIso
    (source (graph core5214) (root 8) 4 2) DegreeTwoThreeSpectrum7556.graph sourceMap5214swap=true := by decide +kernel
theorem fusedMap5214swap_checked : acceptsGraphIso
    (fused (graph core5214) (root 8) 4 2) DegreeTwoThreeSpectrum6047.graph fusedMap5214swap=true := by decide +kernel
theorem certified5214swap : Certified (graph core5214) (root 8) 4 2 :=
  of_native_maps core5214 DegreeTwoThreeSpectrum7556.graph DegreeTwoThreeSpectrum6047.graph
    sourceMap5214swap fusedMap5214swap sourceMap5214swap_checked fusedMap5214swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5214
#print axioms sourceMap5214swap_checked
#print axioms fusedMap5214swap_checked
#print axioms certified5214swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
