/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4016 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap4016 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,8,6,7,1,0,9,10,11,12,13,14] (sourceLabel 4 1 7 v)
def fusedMap4016 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 1 7 v)
theorem sourceMap4016_checked : acceptsGraphIso
    (source (graph core4016) (root 4) 1 7) DegreeTwoThreeSpectrum2383.graph sourceMap4016=true := by decide +kernel
theorem fusedMap4016_checked : acceptsGraphIso
    (fused (graph core4016) (root 4) 1 7) DegreeTwoThreeSpectrum2311.graph fusedMap4016=true := by decide +kernel
theorem certified4016 : Certified (graph core4016) (root 4) 1 7 :=
  of_native_maps core4016 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap4016 fusedMap4016 sourceMap4016_checked fusedMap4016_checked
    DegreeTwoThreeFiniteComparisons.comparison4016
#print axioms sourceMap4016_checked
#print axioms fusedMap4016_checked
#print axioms certified4016
def sourceMap4016swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,8,1,0,9,10,11,12,13,14,6,7] (sourceLabel 4 7 1 v)
def fusedMap4016swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 7 1 v)
theorem sourceMap4016swap_checked : acceptsGraphIso
    (source (graph core4016) (root 4) 7 1) DegreeTwoThreeSpectrum2383.graph sourceMap4016swap=true := by decide +kernel
theorem fusedMap4016swap_checked : acceptsGraphIso
    (fused (graph core4016) (root 4) 7 1) DegreeTwoThreeSpectrum2311.graph fusedMap4016swap=true := by decide +kernel
theorem certified4016swap : Certified (graph core4016) (root 4) 7 1 :=
  of_native_maps core4016 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap4016swap fusedMap4016swap sourceMap4016swap_checked fusedMap4016swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4016
#print axioms sourceMap4016swap_checked
#print axioms fusedMap4016swap_checked
#print axioms certified4016swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
