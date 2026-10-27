/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4672 : Family 10 := level10.get ⟨807,by decide⟩
def sourceMap4672 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4672 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4672_checked : acceptsGraphIso
    (source (graph core4672) (root 10) 2 2) DegreeTwoThreeSpectrum7471.graph sourceMap4672=true := by decide +kernel
theorem fusedMap4672_checked : acceptsGraphIso
    (fused (graph core4672) (root 10) 2 2) DegreeTwoThreeSpectrum5604.graph fusedMap4672=true := by decide +kernel
theorem certified4672 : Certified (graph core4672) (root 10) 2 2 :=
  of_native_maps core4672 DegreeTwoThreeSpectrum7471.graph DegreeTwoThreeSpectrum5604.graph
    sourceMap4672 fusedMap4672 sourceMap4672_checked fusedMap4672_checked
    DegreeTwoThreeFiniteComparisons.comparison4672
#print axioms sourceMap4672_checked
#print axioms fusedMap4672_checked
#print axioms certified4672
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
