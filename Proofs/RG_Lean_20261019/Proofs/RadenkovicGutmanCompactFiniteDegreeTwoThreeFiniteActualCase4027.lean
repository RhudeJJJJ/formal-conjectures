/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4027 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap4027 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,9,7,8,2,1,0,10,11,12,13,14,15] (sourceLabel 4 1 8 v)
def fusedMap4027 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 1 8 v)
theorem sourceMap4027_checked : acceptsGraphIso
    (source (graph core4027) (root 4) 1 8) DegreeTwoThreeSpectrum4071.graph sourceMap4027=true := by decide +kernel
theorem fusedMap4027_checked : acceptsGraphIso
    (fused (graph core4027) (root 4) 1 8) DegreeTwoThreeSpectrum3876.graph fusedMap4027=true := by decide +kernel
theorem certified4027 : Certified (graph core4027) (root 4) 1 8 :=
  of_native_maps core4027 DegreeTwoThreeSpectrum4071.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap4027 fusedMap4027 sourceMap4027_checked fusedMap4027_checked
    DegreeTwoThreeFiniteComparisons.comparison4027
#print axioms sourceMap4027_checked
#print axioms fusedMap4027_checked
#print axioms certified4027
def sourceMap4027swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 2) → Fin 16 :=
  fun v => ![3,4,5,6,9,2,1,0,10,11,12,13,14,15,7,8] (sourceLabel 4 8 1 v)
def fusedMap4027swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 8 1 v)
theorem sourceMap4027swap_checked : acceptsGraphIso
    (source (graph core4027) (root 4) 8 1) DegreeTwoThreeSpectrum4071.graph sourceMap4027swap=true := by decide +kernel
theorem fusedMap4027swap_checked : acceptsGraphIso
    (fused (graph core4027) (root 4) 8 1) DegreeTwoThreeSpectrum3876.graph fusedMap4027swap=true := by decide +kernel
theorem certified4027swap : Certified (graph core4027) (root 4) 8 1 :=
  of_native_maps core4027 DegreeTwoThreeSpectrum4071.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap4027swap fusedMap4027swap sourceMap4027swap_checked fusedMap4027swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4027
#print axioms sourceMap4027swap_checked
#print axioms fusedMap4027swap_checked
#print axioms certified4027swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
