/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4876 : Family 10 := level10.get ⟨1314,by decide⟩
def sourceMap4876 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4876 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4876_checked : acceptsGraphIso
    (source (graph core4876) (root 10) 2 2) DegreeTwoThreeSpectrum7395.graph sourceMap4876=true := by decide +kernel
theorem fusedMap4876_checked : acceptsGraphIso
    (fused (graph core4876) (root 10) 2 2) DegreeTwoThreeSpectrum6615.graph fusedMap4876=true := by decide +kernel
theorem certified4876 : Certified (graph core4876) (root 10) 2 2 :=
  of_native_maps core4876 DegreeTwoThreeSpectrum7395.graph DegreeTwoThreeSpectrum6615.graph
    sourceMap4876 fusedMap4876 sourceMap4876_checked fusedMap4876_checked
    DegreeTwoThreeFiniteComparisons.comparison4876
#print axioms sourceMap4876_checked
#print axioms fusedMap4876_checked
#print axioms certified4876
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
