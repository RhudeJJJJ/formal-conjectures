/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4870 : Family 10 := level10.get ⟨1302,by decide⟩
def sourceMap4870 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4870 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4870_checked : acceptsGraphIso
    (source (graph core4870) (root 10) 2 2) DegreeTwoThreeSpectrum7383.graph sourceMap4870=true := by decide +kernel
theorem fusedMap4870_checked : acceptsGraphIso
    (fused (graph core4870) (root 10) 2 2) DegreeTwoThreeSpectrum6592.graph fusedMap4870=true := by decide +kernel
theorem certified4870 : Certified (graph core4870) (root 10) 2 2 :=
  of_native_maps core4870 DegreeTwoThreeSpectrum7383.graph DegreeTwoThreeSpectrum6592.graph
    sourceMap4870 fusedMap4870 sourceMap4870_checked fusedMap4870_checked
    DegreeTwoThreeFiniteComparisons.comparison4870
#print axioms sourceMap4870_checked
#print axioms fusedMap4870_checked
#print axioms certified4870
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
