/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4007 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap4007 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,8,9,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4007 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4007_checked : acceptsGraphIso
    (source (graph core4007) (root 6) 1 6) DegreeTwoThreeSpectrum4463.graph sourceMap4007=true := by decide +kernel
theorem fusedMap4007_checked : acceptsGraphIso
    (fused (graph core4007) (root 6) 1 6) DegreeTwoThreeSpectrum4008.graph fusedMap4007=true := by decide +kernel
theorem certified4007 : Certified (graph core4007) (root 6) 1 6 :=
  of_native_maps core4007 DegreeTwoThreeSpectrum4463.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap4007 fusedMap4007 sourceMap4007_checked fusedMap4007_checked
    DegreeTwoThreeFiniteComparisons.comparison4007
#print axioms sourceMap4007_checked
#print axioms fusedMap4007_checked
#print axioms certified4007
def sourceMap4007swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,1,0,11,12,13,14,15,8,9] (sourceLabel 6 6 1 v)
def fusedMap4007swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4007swap_checked : acceptsGraphIso
    (source (graph core4007) (root 6) 6 1) DegreeTwoThreeSpectrum4463.graph sourceMap4007swap=true := by decide +kernel
theorem fusedMap4007swap_checked : acceptsGraphIso
    (fused (graph core4007) (root 6) 6 1) DegreeTwoThreeSpectrum4008.graph fusedMap4007swap=true := by decide +kernel
theorem certified4007swap : Certified (graph core4007) (root 6) 6 1 :=
  of_native_maps core4007 DegreeTwoThreeSpectrum4463.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap4007swap fusedMap4007swap sourceMap4007swap_checked fusedMap4007swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4007
#print axioms sourceMap4007swap_checked
#print axioms fusedMap4007swap_checked
#print axioms certified4007swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
