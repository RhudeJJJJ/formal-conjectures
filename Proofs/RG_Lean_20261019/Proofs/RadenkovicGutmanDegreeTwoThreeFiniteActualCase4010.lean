/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4010 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap4010 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4010 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4010_checked : acceptsGraphIso
    (source (graph core4010) (root 6) 1 6) DegreeTwoThreeSpectrum4570.graph sourceMap4010=true := by decide +kernel
theorem fusedMap4010_checked : acceptsGraphIso
    (fused (graph core4010) (root 6) 1 6) DegreeTwoThreeSpectrum4067.graph fusedMap4010=true := by decide +kernel
theorem certified4010 : Certified (graph core4010) (root 6) 1 6 :=
  of_native_maps core4010 DegreeTwoThreeSpectrum4570.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap4010 fusedMap4010 sourceMap4010_checked fusedMap4010_checked
    DegreeTwoThreeFiniteComparisons.comparison4010
#print axioms sourceMap4010_checked
#print axioms fusedMap4010_checked
#print axioms certified4010
def sourceMap4010swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,15,9,10] (sourceLabel 6 6 1 v)
def fusedMap4010swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4010swap_checked : acceptsGraphIso
    (source (graph core4010) (root 6) 6 1) DegreeTwoThreeSpectrum4570.graph sourceMap4010swap=true := by decide +kernel
theorem fusedMap4010swap_checked : acceptsGraphIso
    (fused (graph core4010) (root 6) 6 1) DegreeTwoThreeSpectrum4067.graph fusedMap4010swap=true := by decide +kernel
theorem certified4010swap : Certified (graph core4010) (root 6) 6 1 :=
  of_native_maps core4010 DegreeTwoThreeSpectrum4570.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap4010swap fusedMap4010swap sourceMap4010swap_checked fusedMap4010swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4010
#print axioms sourceMap4010swap_checked
#print axioms fusedMap4010swap_checked
#print axioms certified4010swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
