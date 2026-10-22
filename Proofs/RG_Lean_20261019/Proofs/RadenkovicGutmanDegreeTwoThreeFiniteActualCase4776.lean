/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4776 : Family 10 := level10.get ⟨1074,by decide⟩
def sourceMap4776 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4776 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4776_checked : acceptsGraphIso
    (source (graph core4776) (root 10) 2 2) DegreeTwoThreeSpectrum7155.graph sourceMap4776=true := by decide +kernel
theorem fusedMap4776_checked : acceptsGraphIso
    (fused (graph core4776) (root 10) 2 2) DegreeTwoThreeSpectrum6133.graph fusedMap4776=true := by decide +kernel
theorem certified4776 : Certified (graph core4776) (root 10) 2 2 :=
  of_native_maps core4776 DegreeTwoThreeSpectrum7155.graph DegreeTwoThreeSpectrum6133.graph
    sourceMap4776 fusedMap4776 sourceMap4776_checked fusedMap4776_checked
    DegreeTwoThreeFiniteComparisons.comparison4776
#print axioms sourceMap4776_checked
#print axioms fusedMap4776_checked
#print axioms certified4776
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
