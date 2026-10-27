/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4026 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap4026 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,8,6,7,2,1,0,9,10,11,12,13,14] (sourceLabel 3 1 8 v)
def fusedMap4026 : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 1 8 v)
theorem sourceMap4026_checked : acceptsGraphIso
    (source (graph core4026) (root 3) 1 8) DegreeTwoThreeSpectrum2349.graph sourceMap4026=true := by decide +kernel
theorem fusedMap4026_checked : acceptsGraphIso
    (fused (graph core4026) (root 3) 1 8) DegreeTwoThreeSpectrum2310.graph fusedMap4026=true := by decide +kernel
theorem certified4026 : Certified (graph core4026) (root 3) 1 8 :=
  of_native_maps core4026 DegreeTwoThreeSpectrum2349.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap4026 fusedMap4026 sourceMap4026_checked fusedMap4026_checked
    DegreeTwoThreeFiniteComparisons.comparison4026
#print axioms sourceMap4026_checked
#print axioms fusedMap4026_checked
#print axioms certified4026
def sourceMap4026swap : (Vertices 3 ⊕ Fin 9 ⊕ Fin 2) → Fin 15 :=
  fun v => ![3,4,5,8,2,1,0,9,10,11,12,13,14,6,7] (sourceLabel 3 8 1 v)
def fusedMap4026swap : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 8 1 v)
theorem sourceMap4026swap_checked : acceptsGraphIso
    (source (graph core4026) (root 3) 8 1) DegreeTwoThreeSpectrum2349.graph sourceMap4026swap=true := by decide +kernel
theorem fusedMap4026swap_checked : acceptsGraphIso
    (fused (graph core4026) (root 3) 8 1) DegreeTwoThreeSpectrum2310.graph fusedMap4026swap=true := by decide +kernel
theorem certified4026swap : Certified (graph core4026) (root 3) 8 1 :=
  of_native_maps core4026 DegreeTwoThreeSpectrum2349.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap4026swap fusedMap4026swap sourceMap4026swap_checked fusedMap4026swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4026
#print axioms sourceMap4026swap_checked
#print axioms fusedMap4026swap_checked
#print axioms certified4026swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
