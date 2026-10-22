/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2558 : Family 10 := level10.get ⟨410,by decide⟩
def sourceMap2558 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2558 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2558_checked : acceptsGraphIso
    (source (graph core2558) (root 10) 0 4) DegreeTwoThreeSpectrum5781.graph sourceMap2558=true := by decide +kernel
theorem fusedMap2558_checked : acceptsGraphIso
    (fused (graph core2558) (root 10) 0 4) DegreeTwoThreeSpectrum5782.graph fusedMap2558=true := by decide +kernel
theorem certified2558 : Certified (graph core2558) (root 10) 0 4 :=
  of_native_maps core2558 DegreeTwoThreeSpectrum5781.graph DegreeTwoThreeSpectrum5782.graph
    sourceMap2558 fusedMap2558 sourceMap2558_checked fusedMap2558_checked
    DegreeTwoThreeFiniteComparisons.comparison2558
#print axioms sourceMap2558_checked
#print axioms fusedMap2558_checked
#print axioms certified2558
def sourceMap2558swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2558swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2558swap_checked : acceptsGraphIso
    (source (graph core2558) (root 10) 4 0) DegreeTwoThreeSpectrum5781.graph sourceMap2558swap=true := by decide +kernel
theorem fusedMap2558swap_checked : acceptsGraphIso
    (fused (graph core2558) (root 10) 4 0) DegreeTwoThreeSpectrum5782.graph fusedMap2558swap=true := by decide +kernel
theorem certified2558swap : Certified (graph core2558) (root 10) 4 0 :=
  of_native_maps core2558 DegreeTwoThreeSpectrum5781.graph DegreeTwoThreeSpectrum5782.graph
    sourceMap2558swap fusedMap2558swap sourceMap2558swap_checked fusedMap2558swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2558
#print axioms sourceMap2558swap_checked
#print axioms fusedMap2558swap_checked
#print axioms certified2558swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
