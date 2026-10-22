/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4017 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap4017 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,9,7,8,2,1,0,10,11,12,13,14] (sourceLabel 4 1 7 v)
def fusedMap4017 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 1 7 v)
theorem sourceMap4017_checked : acceptsGraphIso
    (source (graph core4017) (root 4) 1 7) DegreeTwoThreeSpectrum2509.graph sourceMap4017=true := by decide +kernel
theorem fusedMap4017_checked : acceptsGraphIso
    (fused (graph core4017) (root 4) 1 7) DegreeTwoThreeSpectrum2327.graph fusedMap4017=true := by decide +kernel
theorem certified4017 : Certified (graph core4017) (root 4) 1 7 :=
  of_native_maps core4017 DegreeTwoThreeSpectrum2509.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap4017 fusedMap4017 sourceMap4017_checked fusedMap4017_checked
    DegreeTwoThreeFiniteComparisons.comparison4017
#print axioms sourceMap4017_checked
#print axioms fusedMap4017_checked
#print axioms certified4017
def sourceMap4017swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 2) → Fin 15 :=
  fun v => ![3,4,5,6,9,2,1,0,10,11,12,13,14,7,8] (sourceLabel 4 7 1 v)
def fusedMap4017swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 7 1 v)
theorem sourceMap4017swap_checked : acceptsGraphIso
    (source (graph core4017) (root 4) 7 1) DegreeTwoThreeSpectrum2509.graph sourceMap4017swap=true := by decide +kernel
theorem fusedMap4017swap_checked : acceptsGraphIso
    (fused (graph core4017) (root 4) 7 1) DegreeTwoThreeSpectrum2327.graph fusedMap4017swap=true := by decide +kernel
theorem certified4017swap : Certified (graph core4017) (root 4) 7 1 :=
  of_native_maps core4017 DegreeTwoThreeSpectrum2509.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap4017swap fusedMap4017swap sourceMap4017swap_checked fusedMap4017swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4017
#print axioms sourceMap4017swap_checked
#print axioms fusedMap4017swap_checked
#print axioms certified4017swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
