/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4019 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap4019 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13,14,15] (sourceLabel 5 1 7 v)
def fusedMap4019 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 1 7 v)
theorem sourceMap4019_checked : acceptsGraphIso
    (source (graph core4019) (root 5) 1 7) DegreeTwoThreeSpectrum4127.graph sourceMap4019=true := by decide +kernel
theorem fusedMap4019_checked : acceptsGraphIso
    (fused (graph core4019) (root 5) 1 7) DegreeTwoThreeSpectrum3882.graph fusedMap4019=true := by decide +kernel
theorem certified4019 : Certified (graph core4019) (root 5) 1 7 :=
  of_native_maps core4019 DegreeTwoThreeSpectrum4127.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap4019 fusedMap4019 sourceMap4019_checked fusedMap4019_checked
    DegreeTwoThreeFiniteComparisons.comparison4019
#print axioms sourceMap4019_checked
#print axioms fusedMap4019_checked
#print axioms certified4019
def sourceMap4019swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,14,15,7,8] (sourceLabel 5 7 1 v)
def fusedMap4019swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 7 1 v)
theorem sourceMap4019swap_checked : acceptsGraphIso
    (source (graph core4019) (root 5) 7 1) DegreeTwoThreeSpectrum4127.graph sourceMap4019swap=true := by decide +kernel
theorem fusedMap4019swap_checked : acceptsGraphIso
    (fused (graph core4019) (root 5) 7 1) DegreeTwoThreeSpectrum3882.graph fusedMap4019swap=true := by decide +kernel
theorem certified4019swap : Certified (graph core4019) (root 5) 7 1 :=
  of_native_maps core4019 DegreeTwoThreeSpectrum4127.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap4019swap fusedMap4019swap sourceMap4019swap_checked fusedMap4019swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4019
#print axioms sourceMap4019swap_checked
#print axioms fusedMap4019swap_checked
#print axioms certified4019swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
