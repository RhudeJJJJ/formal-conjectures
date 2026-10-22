/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2985 : Family 10 := level10.get ⟨1535,by decide⟩
def sourceMap2985 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2985 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2985_checked : acceptsGraphIso
    (source (graph core2985) (root 10) 0 4) DegreeTwoThreeSpectrum7073.graph sourceMap2985=true := by decide +kernel
theorem fusedMap2985_checked : acceptsGraphIso
    (fused (graph core2985) (root 10) 0 4) DegreeTwoThreeSpectrum5975.graph fusedMap2985=true := by decide +kernel
theorem certified2985 : Certified (graph core2985) (root 10) 0 4 :=
  of_native_maps core2985 DegreeTwoThreeSpectrum7073.graph DegreeTwoThreeSpectrum5975.graph
    sourceMap2985 fusedMap2985 sourceMap2985_checked fusedMap2985_checked
    DegreeTwoThreeFiniteComparisons.comparison2985
#print axioms sourceMap2985_checked
#print axioms fusedMap2985_checked
#print axioms certified2985
def sourceMap2985swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2985swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2985swap_checked : acceptsGraphIso
    (source (graph core2985) (root 10) 4 0) DegreeTwoThreeSpectrum7073.graph sourceMap2985swap=true := by decide +kernel
theorem fusedMap2985swap_checked : acceptsGraphIso
    (fused (graph core2985) (root 10) 4 0) DegreeTwoThreeSpectrum5975.graph fusedMap2985swap=true := by decide +kernel
theorem certified2985swap : Certified (graph core2985) (root 10) 4 0 :=
  of_native_maps core2985 DegreeTwoThreeSpectrum7073.graph DegreeTwoThreeSpectrum5975.graph
    sourceMap2985swap fusedMap2985swap sourceMap2985swap_checked fusedMap2985swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2985
#print axioms sourceMap2985swap_checked
#print axioms fusedMap2985swap_checked
#print axioms certified2985swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
