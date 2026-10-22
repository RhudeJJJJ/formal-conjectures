/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4728 : Family 10 := level10.get ⟨951,by decide⟩
def sourceMap4728 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4728 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4728_checked : acceptsGraphIso
    (source (graph core4728) (root 10) 2 2) DegreeTwoThreeSpectrum7551.graph sourceMap4728=true := by decide +kernel
theorem fusedMap4728_checked : acceptsGraphIso
    (fused (graph core4728) (root 10) 2 2) DegreeTwoThreeSpectrum5851.graph fusedMap4728=true := by decide +kernel
theorem certified4728 : Certified (graph core4728) (root 10) 2 2 :=
  of_native_maps core4728 DegreeTwoThreeSpectrum7551.graph DegreeTwoThreeSpectrum5851.graph
    sourceMap4728 fusedMap4728 sourceMap4728_checked fusedMap4728_checked
    DegreeTwoThreeFiniteComparisons.comparison4728
#print axioms sourceMap4728_checked
#print axioms fusedMap4728_checked
#print axioms certified4728
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
