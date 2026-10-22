/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2129 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap2129 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2129 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2129_checked : acceptsGraphIso
    (source (graph core2129) (root 8) 0 4) DegreeTwoThreeSpectrum2626.graph sourceMap2129=true := by decide +kernel
theorem fusedMap2129_checked : acceptsGraphIso
    (fused (graph core2129) (root 8) 0 4) DegreeTwoThreeSpectrum2336.graph fusedMap2129=true := by decide +kernel
theorem certified2129 : Certified (graph core2129) (root 8) 0 4 :=
  of_native_maps core2129 DegreeTwoThreeSpectrum2626.graph DegreeTwoThreeSpectrum2336.graph
    sourceMap2129 fusedMap2129 sourceMap2129_checked fusedMap2129_checked
    DegreeTwoThreeFiniteComparisons.comparison2129
#print axioms sourceMap2129_checked
#print axioms fusedMap2129_checked
#print axioms certified2129
def sourceMap2129swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2129swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2129swap_checked : acceptsGraphIso
    (source (graph core2129) (root 8) 4 0) DegreeTwoThreeSpectrum2626.graph sourceMap2129swap=true := by decide +kernel
theorem fusedMap2129swap_checked : acceptsGraphIso
    (fused (graph core2129) (root 8) 4 0) DegreeTwoThreeSpectrum2336.graph fusedMap2129swap=true := by decide +kernel
theorem certified2129swap : Certified (graph core2129) (root 8) 4 0 :=
  of_native_maps core2129 DegreeTwoThreeSpectrum2626.graph DegreeTwoThreeSpectrum2336.graph
    sourceMap2129swap fusedMap2129swap sourceMap2129swap_checked fusedMap2129swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2129
#print axioms sourceMap2129swap_checked
#print axioms fusedMap2129swap_checked
#print axioms certified2129swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
