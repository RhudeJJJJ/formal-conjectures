/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2577 : Family 10 := level10.get ⟨463,by decide⟩
def sourceMap2577 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2577 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2577_checked : acceptsGraphIso
    (source (graph core2577) (root 10) 0 4) DegreeTwoThreeSpectrum5902.graph sourceMap2577=true := by decide +kernel
theorem fusedMap2577_checked : acceptsGraphIso
    (fused (graph core2577) (root 10) 0 4) DegreeTwoThreeSpectrum5906.graph fusedMap2577=true := by decide +kernel
theorem certified2577 : Certified (graph core2577) (root 10) 0 4 :=
  of_native_maps core2577 DegreeTwoThreeSpectrum5902.graph DegreeTwoThreeSpectrum5906.graph
    sourceMap2577 fusedMap2577 sourceMap2577_checked fusedMap2577_checked
    DegreeTwoThreeFiniteComparisons.comparison2577
#print axioms sourceMap2577_checked
#print axioms fusedMap2577_checked
#print axioms certified2577
def sourceMap2577swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2577swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2577swap_checked : acceptsGraphIso
    (source (graph core2577) (root 10) 4 0) DegreeTwoThreeSpectrum5902.graph sourceMap2577swap=true := by decide +kernel
theorem fusedMap2577swap_checked : acceptsGraphIso
    (fused (graph core2577) (root 10) 4 0) DegreeTwoThreeSpectrum5906.graph fusedMap2577swap=true := by decide +kernel
theorem certified2577swap : Certified (graph core2577) (root 10) 4 0 :=
  of_native_maps core2577 DegreeTwoThreeSpectrum5902.graph DegreeTwoThreeSpectrum5906.graph
    sourceMap2577swap fusedMap2577swap sourceMap2577swap_checked fusedMap2577swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2577
#print axioms sourceMap2577swap_checked
#print axioms fusedMap2577swap_checked
#print axioms certified2577swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
