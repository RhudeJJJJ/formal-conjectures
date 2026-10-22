/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4994 : Family 10 := level10.get ⟨1602,by decide⟩
def sourceMap4994 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4994 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4994_checked : acceptsGraphIso
    (source (graph core4994) (root 10) 2 2) DegreeTwoThreeSpectrum7595.graph sourceMap4994=true := by decide +kernel
theorem fusedMap4994_checked : acceptsGraphIso
    (fused (graph core4994) (root 10) 2 2) DegreeTwoThreeSpectrum6118.graph fusedMap4994=true := by decide +kernel
theorem certified4994 : Certified (graph core4994) (root 10) 2 2 :=
  of_native_maps core4994 DegreeTwoThreeSpectrum7595.graph DegreeTwoThreeSpectrum6118.graph
    sourceMap4994 fusedMap4994 sourceMap4994_checked fusedMap4994_checked
    DegreeTwoThreeFiniteComparisons.comparison4994
#print axioms sourceMap4994_checked
#print axioms fusedMap4994_checked
#print axioms certified4994
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
