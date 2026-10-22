/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3139 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap3139 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3139 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3139_checked : acceptsGraphIso
    (source (graph core3139) (root 7) 0 5) DegreeTwoThreeSpectrum3064.graph sourceMap3139=true := by decide +kernel
theorem fusedMap3139_checked : acceptsGraphIso
    (fused (graph core3139) (root 7) 0 5) DegreeTwoThreeSpectrum2455.graph fusedMap3139=true := by decide +kernel
theorem certified3139 : Certified (graph core3139) (root 7) 0 5 :=
  of_native_maps core3139 DegreeTwoThreeSpectrum3064.graph DegreeTwoThreeSpectrum2455.graph
    sourceMap3139 fusedMap3139 sourceMap3139_checked fusedMap3139_checked
    DegreeTwoThreeFiniteComparisons.comparison3139
#print axioms sourceMap3139_checked
#print axioms fusedMap3139_checked
#print axioms certified3139
def sourceMap3139swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,10] (sourceLabel 7 5 0 v)
def fusedMap3139swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3139swap_checked : acceptsGraphIso
    (source (graph core3139) (root 7) 5 0) DegreeTwoThreeSpectrum3064.graph sourceMap3139swap=true := by decide +kernel
theorem fusedMap3139swap_checked : acceptsGraphIso
    (fused (graph core3139) (root 7) 5 0) DegreeTwoThreeSpectrum2455.graph fusedMap3139swap=true := by decide +kernel
theorem certified3139swap : Certified (graph core3139) (root 7) 5 0 :=
  of_native_maps core3139 DegreeTwoThreeSpectrum3064.graph DegreeTwoThreeSpectrum2455.graph
    sourceMap3139swap fusedMap3139swap sourceMap3139swap_checked fusedMap3139swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3139
#print axioms sourceMap3139swap_checked
#print axioms fusedMap3139swap_checked
#print axioms certified3139swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
