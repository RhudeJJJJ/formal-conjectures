/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1402 : Family 9 := level9.get ⟨147,by decide⟩
def sourceMap1402 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1402 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1402_checked : acceptsGraphIso
    (source (graph core1402) (root 9) 0 1) DegreeOneSmallSpectrum1042.graph sourceMap1402=true := by decide +kernel
theorem fusedMap1402_checked : acceptsGraphIso
    (fused (graph core1402) (root 9) 0 1) DegreeOneSmallSpectrum1044.graph fusedMap1402=true := by decide +kernel
theorem certified1402 : Certified (graph core1402) (root 9) 0 1 :=
  of_native_maps core1402 DegreeOneSmallSpectrum1042.graph DegreeOneSmallSpectrum1044.graph
    sourceMap1402 fusedMap1402 sourceMap1402_checked fusedMap1402_checked
    DegreeOneSmallComparisons.comparison1402
#print axioms sourceMap1402_checked
#print axioms fusedMap1402_checked
#print axioms certified1402
def sourceMap1402swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1402swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1402swap_checked : acceptsGraphIso
    (source (graph core1402) (root 9) 1 0) DegreeOneSmallSpectrum1042.graph sourceMap1402swap=true := by decide +kernel
theorem fusedMap1402swap_checked : acceptsGraphIso
    (fused (graph core1402) (root 9) 1 0) DegreeOneSmallSpectrum1044.graph fusedMap1402swap=true := by decide +kernel
theorem certified1402swap : Certified (graph core1402) (root 9) 1 0 :=
  of_native_maps core1402 DegreeOneSmallSpectrum1042.graph DegreeOneSmallSpectrum1044.graph
    sourceMap1402swap fusedMap1402swap sourceMap1402swap_checked fusedMap1402swap_checked
    DegreeOneSmallComparisons.comparison1402
#print axioms sourceMap1402swap_checked
#print axioms fusedMap1402swap_checked
#print axioms certified1402swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
