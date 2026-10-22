/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4626 : Family 10 := level10.get ⟨671,by decide⟩
def sourceMap4626 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,16,13,14,15,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4626 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4626_checked : acceptsGraphIso
    (source (graph core4626) (root 10) 2 2) DegreeTwoThreeSpectrum7314.graph sourceMap4626=true := by decide +kernel
theorem fusedMap4626_checked : acceptsGraphIso
    (fused (graph core4626) (root 10) 2 2) DegreeTwoThreeSpectrum5386.graph fusedMap4626=true := by decide +kernel
theorem certified4626 : Certified (graph core4626) (root 10) 2 2 :=
  of_native_maps core4626 DegreeTwoThreeSpectrum7314.graph DegreeTwoThreeSpectrum5386.graph
    sourceMap4626 fusedMap4626 sourceMap4626_checked fusedMap4626_checked
    DegreeTwoThreeFiniteComparisons.comparison4626
#print axioms sourceMap4626_checked
#print axioms fusedMap4626_checked
#print axioms certified4626
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
