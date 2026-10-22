/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4769 : Family 10 := level10.get ⟨1056,by decide⟩
def sourceMap4769 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4769 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4769_checked : acceptsGraphIso
    (source (graph core4769) (root 10) 2 2) DegreeTwoThreeSpectrum7135.graph sourceMap4769=true := by decide +kernel
theorem fusedMap4769_checked : acceptsGraphIso
    (fused (graph core4769) (root 10) 2 2) DegreeTwoThreeSpectrum6099.graph fusedMap4769=true := by decide +kernel
theorem certified4769 : Certified (graph core4769) (root 10) 2 2 :=
  of_native_maps core4769 DegreeTwoThreeSpectrum7135.graph DegreeTwoThreeSpectrum6099.graph
    sourceMap4769 fusedMap4769 sourceMap4769_checked fusedMap4769_checked
    DegreeTwoThreeFiniteComparisons.comparison4769
#print axioms sourceMap4769_checked
#print axioms fusedMap4769_checked
#print axioms certified4769
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
