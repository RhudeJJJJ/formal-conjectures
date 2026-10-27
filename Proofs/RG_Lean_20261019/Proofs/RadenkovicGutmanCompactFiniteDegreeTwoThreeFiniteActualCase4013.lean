/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4013 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap4013 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4013 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4013_checked : acceptsGraphIso
    (source (graph core4013) (root 6) 1 6) DegreeTwoThreeSpectrum4259.graph sourceMap4013=true := by decide +kernel
theorem fusedMap4013_checked : acceptsGraphIso
    (fused (graph core4013) (root 6) 1 6) DegreeTwoThreeSpectrum3917.graph fusedMap4013=true := by decide +kernel
theorem certified4013 : Certified (graph core4013) (root 6) 1 6 :=
  of_native_maps core4013 DegreeTwoThreeSpectrum4259.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap4013 fusedMap4013 sourceMap4013_checked fusedMap4013_checked
    DegreeTwoThreeFiniteComparisons.comparison4013
#print axioms sourceMap4013_checked
#print axioms fusedMap4013_checked
#print axioms certified4013
def sourceMap4013swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,15,9,10] (sourceLabel 6 6 1 v)
def fusedMap4013swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4013swap_checked : acceptsGraphIso
    (source (graph core4013) (root 6) 6 1) DegreeTwoThreeSpectrum4259.graph sourceMap4013swap=true := by decide +kernel
theorem fusedMap4013swap_checked : acceptsGraphIso
    (fused (graph core4013) (root 6) 6 1) DegreeTwoThreeSpectrum3917.graph fusedMap4013swap=true := by decide +kernel
theorem certified4013swap : Certified (graph core4013) (root 6) 6 1 :=
  of_native_maps core4013 DegreeTwoThreeSpectrum4259.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap4013swap fusedMap4013swap sourceMap4013swap_checked fusedMap4013swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4013
#print axioms sourceMap4013swap_checked
#print axioms fusedMap4013swap_checked
#print axioms certified4013swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
