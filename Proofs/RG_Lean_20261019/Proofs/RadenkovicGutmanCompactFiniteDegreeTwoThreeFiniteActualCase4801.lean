/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4801 : Family 10 := level10.get ⟨1137,by decide⟩
def sourceMap4801 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4801 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4801_checked : acceptsGraphIso
    (source (graph core4801) (root 10) 2 2) DegreeTwoThreeSpectrum7220.graph sourceMap4801=true := by decide +kernel
theorem fusedMap4801_checked : acceptsGraphIso
    (fused (graph core4801) (root 10) 2 2) DegreeTwoThreeSpectrum6263.graph fusedMap4801=true := by decide +kernel
theorem certified4801 : Certified (graph core4801) (root 10) 2 2 :=
  of_native_maps core4801 DegreeTwoThreeSpectrum7220.graph DegreeTwoThreeSpectrum6263.graph
    sourceMap4801 fusedMap4801 sourceMap4801_checked fusedMap4801_checked
    DegreeTwoThreeFiniteComparisons.comparison4801
#print axioms sourceMap4801_checked
#print axioms fusedMap4801_checked
#print axioms certified4801
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
