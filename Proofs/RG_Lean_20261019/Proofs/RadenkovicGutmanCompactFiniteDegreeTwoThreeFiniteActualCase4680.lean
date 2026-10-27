/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4680 : Family 10 := level10.get ⟨822,by decide⟩
def sourceMap4680 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4680 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4680_checked : acceptsGraphIso
    (source (graph core4680) (root 10) 2 2) DegreeTwoThreeSpectrum7269.graph sourceMap4680=true := by decide +kernel
theorem fusedMap4680_checked : acceptsGraphIso
    (fused (graph core4680) (root 10) 2 2) DegreeTwoThreeSpectrum5631.graph fusedMap4680=true := by decide +kernel
theorem certified4680 : Certified (graph core4680) (root 10) 2 2 :=
  of_native_maps core4680 DegreeTwoThreeSpectrum7269.graph DegreeTwoThreeSpectrum5631.graph
    sourceMap4680 fusedMap4680 sourceMap4680_checked fusedMap4680_checked
    DegreeTwoThreeFiniteComparisons.comparison4680
#print axioms sourceMap4680_checked
#print axioms fusedMap4680_checked
#print axioms certified4680
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
