/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2380 : Family 9 := level9.get ⟨497,by decide⟩
def sourceMap2380 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2380 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2380_checked : acceptsGraphIso
    (source (graph core2380) (root 9) 0 4) DegreeTwoThreeSpectrum4573.graph sourceMap2380=true := by decide +kernel
theorem fusedMap2380_checked : acceptsGraphIso
    (fused (graph core2380) (root 9) 0 4) DegreeTwoThreeSpectrum4574.graph fusedMap2380=true := by decide +kernel
theorem certified2380 : Certified (graph core2380) (root 9) 0 4 :=
  of_native_maps core2380 DegreeTwoThreeSpectrum4573.graph DegreeTwoThreeSpectrum4574.graph
    sourceMap2380 fusedMap2380 sourceMap2380_checked fusedMap2380_checked
    DegreeTwoThreeFiniteComparisons.comparison2380
#print axioms sourceMap2380_checked
#print axioms fusedMap2380_checked
#print axioms certified2380
def sourceMap2380swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2380swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2380swap_checked : acceptsGraphIso
    (source (graph core2380) (root 9) 4 0) DegreeTwoThreeSpectrum4573.graph sourceMap2380swap=true := by decide +kernel
theorem fusedMap2380swap_checked : acceptsGraphIso
    (fused (graph core2380) (root 9) 4 0) DegreeTwoThreeSpectrum4574.graph fusedMap2380swap=true := by decide +kernel
theorem certified2380swap : Certified (graph core2380) (root 9) 4 0 :=
  of_native_maps core2380 DegreeTwoThreeSpectrum4573.graph DegreeTwoThreeSpectrum4574.graph
    sourceMap2380swap fusedMap2380swap sourceMap2380swap_checked fusedMap2380swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2380
#print axioms sourceMap2380swap_checked
#print axioms fusedMap2380swap_checked
#print axioms certified2380swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
