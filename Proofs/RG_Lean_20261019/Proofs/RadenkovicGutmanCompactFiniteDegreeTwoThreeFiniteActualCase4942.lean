/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4942 : Family 10 := level10.get ⟨1466,by decide⟩
def sourceMap4942 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4942 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4942_checked : acceptsGraphIso
    (source (graph core4942) (root 10) 2 2) DegreeTwoThreeSpectrum7558.graph sourceMap4942=true := by decide +kernel
theorem fusedMap4942_checked : acceptsGraphIso
    (fused (graph core4942) (root 10) 2 2) DegreeTwoThreeSpectrum6945.graph fusedMap4942=true := by decide +kernel
theorem certified4942 : Certified (graph core4942) (root 10) 2 2 :=
  of_native_maps core4942 DegreeTwoThreeSpectrum7558.graph DegreeTwoThreeSpectrum6945.graph
    sourceMap4942 fusedMap4942 sourceMap4942_checked fusedMap4942_checked
    DegreeTwoThreeFiniteComparisons.comparison4942
#print axioms sourceMap4942_checked
#print axioms fusedMap4942_checked
#print axioms certified4942
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
