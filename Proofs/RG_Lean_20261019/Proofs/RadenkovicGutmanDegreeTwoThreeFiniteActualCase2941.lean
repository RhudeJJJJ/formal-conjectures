/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2941 : Family 10 := level10.get ⟨1414,by decide⟩
def sourceMap2941 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2941 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2941_checked : acceptsGraphIso
    (source (graph core2941) (root 10) 0 4) DegreeTwoThreeSpectrum6860.graph sourceMap2941=true := by decide +kernel
theorem fusedMap2941_checked : acceptsGraphIso
    (fused (graph core2941) (root 10) 0 4) DegreeTwoThreeSpectrum6861.graph fusedMap2941=true := by decide +kernel
theorem certified2941 : Certified (graph core2941) (root 10) 0 4 :=
  of_native_maps core2941 DegreeTwoThreeSpectrum6860.graph DegreeTwoThreeSpectrum6861.graph
    sourceMap2941 fusedMap2941 sourceMap2941_checked fusedMap2941_checked
    DegreeTwoThreeFiniteComparisons.comparison2941
#print axioms sourceMap2941_checked
#print axioms fusedMap2941_checked
#print axioms certified2941
def sourceMap2941swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2941swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2941swap_checked : acceptsGraphIso
    (source (graph core2941) (root 10) 4 0) DegreeTwoThreeSpectrum6860.graph sourceMap2941swap=true := by decide +kernel
theorem fusedMap2941swap_checked : acceptsGraphIso
    (fused (graph core2941) (root 10) 4 0) DegreeTwoThreeSpectrum6861.graph fusedMap2941swap=true := by decide +kernel
theorem certified2941swap : Certified (graph core2941) (root 10) 4 0 :=
  of_native_maps core2941 DegreeTwoThreeSpectrum6860.graph DegreeTwoThreeSpectrum6861.graph
    sourceMap2941swap fusedMap2941swap sourceMap2941swap_checked fusedMap2941swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2941
#print axioms sourceMap2941swap_checked
#print axioms fusedMap2941swap_checked
#print axioms certified2941swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
