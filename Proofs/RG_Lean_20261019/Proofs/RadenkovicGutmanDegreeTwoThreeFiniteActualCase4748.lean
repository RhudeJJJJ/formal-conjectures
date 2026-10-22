/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4748 : Family 10 := level10.get ⟨988,by decide⟩
def sourceMap4748 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,13,14,15,16,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4748 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4748_checked : acceptsGraphIso
    (source (graph core4748) (root 10) 2 2) DegreeTwoThreeSpectrum7486.graph sourceMap4748=true := by decide +kernel
theorem fusedMap4748_checked : acceptsGraphIso
    (fused (graph core4748) (root 10) 2 2) DegreeTwoThreeSpectrum5928.graph fusedMap4748=true := by decide +kernel
theorem certified4748 : Certified (graph core4748) (root 10) 2 2 :=
  of_native_maps core4748 DegreeTwoThreeSpectrum7486.graph DegreeTwoThreeSpectrum5928.graph
    sourceMap4748 fusedMap4748 sourceMap4748_checked fusedMap4748_checked
    DegreeTwoThreeFiniteComparisons.comparison4748
#print axioms sourceMap4748_checked
#print axioms fusedMap4748_checked
#print axioms certified4748
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
