/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4008 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap4008 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4008 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4008_checked : acceptsGraphIso
    (source (graph core4008) (root 6) 1 6) DegreeTwoThreeSpectrum4494.graph sourceMap4008=true := by decide +kernel
theorem fusedMap4008_checked : acceptsGraphIso
    (fused (graph core4008) (root 6) 1 6) DegreeTwoThreeSpectrum4023.graph fusedMap4008=true := by decide +kernel
theorem certified4008 : Certified (graph core4008) (root 6) 1 6 :=
  of_native_maps core4008 DegreeTwoThreeSpectrum4494.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap4008 fusedMap4008 sourceMap4008_checked fusedMap4008_checked
    DegreeTwoThreeFiniteComparisons.comparison4008
#print axioms sourceMap4008_checked
#print axioms fusedMap4008_checked
#print axioms certified4008
def sourceMap4008swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,15,9,10] (sourceLabel 6 6 1 v)
def fusedMap4008swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4008swap_checked : acceptsGraphIso
    (source (graph core4008) (root 6) 6 1) DegreeTwoThreeSpectrum4494.graph sourceMap4008swap=true := by decide +kernel
theorem fusedMap4008swap_checked : acceptsGraphIso
    (fused (graph core4008) (root 6) 6 1) DegreeTwoThreeSpectrum4023.graph fusedMap4008swap=true := by decide +kernel
theorem certified4008swap : Certified (graph core4008) (root 6) 6 1 :=
  of_native_maps core4008 DegreeTwoThreeSpectrum4494.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap4008swap fusedMap4008swap sourceMap4008swap_checked fusedMap4008swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4008
#print axioms sourceMap4008swap_checked
#print axioms fusedMap4008swap_checked
#print axioms certified4008swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
