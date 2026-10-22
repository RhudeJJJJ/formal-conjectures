/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4877 : Family 10 := level10.get ⟨1319,by decide⟩
def sourceMap4877 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4877 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4877_checked : acceptsGraphIso
    (source (graph core4877) (root 10) 2 2) DegreeTwoThreeSpectrum7403.graph sourceMap4877=true := by decide +kernel
theorem fusedMap4877_checked : acceptsGraphIso
    (fused (graph core4877) (root 10) 2 2) DegreeTwoThreeSpectrum6626.graph fusedMap4877=true := by decide +kernel
theorem certified4877 : Certified (graph core4877) (root 10) 2 2 :=
  of_native_maps core4877 DegreeTwoThreeSpectrum7403.graph DegreeTwoThreeSpectrum6626.graph
    sourceMap4877 fusedMap4877 sourceMap4877_checked fusedMap4877_checked
    DegreeTwoThreeFiniteComparisons.comparison4877
#print axioms sourceMap4877_checked
#print axioms fusedMap4877_checked
#print axioms certified4877
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
