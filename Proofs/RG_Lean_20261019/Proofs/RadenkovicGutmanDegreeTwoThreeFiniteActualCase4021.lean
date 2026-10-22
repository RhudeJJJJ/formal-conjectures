/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4021 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap4021 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13,14,15] (sourceLabel 5 1 7 v)
def fusedMap4021 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 1 7 v)
theorem sourceMap4021_checked : acceptsGraphIso
    (source (graph core4021) (root 5) 1 7) DegreeTwoThreeSpectrum4020.graph sourceMap4021=true := by decide +kernel
theorem fusedMap4021_checked : acceptsGraphIso
    (fused (graph core4021) (root 5) 1 7) DegreeTwoThreeSpectrum3864.graph fusedMap4021=true := by decide +kernel
theorem certified4021 : Certified (graph core4021) (root 5) 1 7 :=
  of_native_maps core4021 DegreeTwoThreeSpectrum4020.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap4021 fusedMap4021 sourceMap4021_checked fusedMap4021_checked
    DegreeTwoThreeFiniteComparisons.comparison4021
#print axioms sourceMap4021_checked
#print axioms fusedMap4021_checked
#print axioms certified4021
def sourceMap4021swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,14,15,7,8] (sourceLabel 5 7 1 v)
def fusedMap4021swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 7 1 v)
theorem sourceMap4021swap_checked : acceptsGraphIso
    (source (graph core4021) (root 5) 7 1) DegreeTwoThreeSpectrum4020.graph sourceMap4021swap=true := by decide +kernel
theorem fusedMap4021swap_checked : acceptsGraphIso
    (fused (graph core4021) (root 5) 7 1) DegreeTwoThreeSpectrum3864.graph fusedMap4021swap=true := by decide +kernel
theorem certified4021swap : Certified (graph core4021) (root 5) 7 1 :=
  of_native_maps core4021 DegreeTwoThreeSpectrum4020.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap4021swap fusedMap4021swap sourceMap4021swap_checked fusedMap4021swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4021
#print axioms sourceMap4021swap_checked
#print axioms fusedMap4021swap_checked
#print axioms certified4021swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
