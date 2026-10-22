/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4535 : Family 10 := level10.get ⟨407,by decide⟩
def sourceMap4535 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4535 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4535_checked : acceptsGraphIso
    (source (graph core4535) (root 10) 2 2) DegreeTwoThreeSpectrum6845.graph sourceMap4535=true := by decide +kernel
theorem fusedMap4535_checked : acceptsGraphIso
    (fused (graph core4535) (root 10) 2 2) DegreeTwoThreeSpectrum5776.graph fusedMap4535=true := by decide +kernel
theorem certified4535 : Certified (graph core4535) (root 10) 2 2 :=
  of_native_maps core4535 DegreeTwoThreeSpectrum6845.graph DegreeTwoThreeSpectrum5776.graph
    sourceMap4535 fusedMap4535 sourceMap4535_checked fusedMap4535_checked
    DegreeTwoThreeFiniteComparisons.comparison4535
#print axioms sourceMap4535_checked
#print axioms fusedMap4535_checked
#print axioms certified4535
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
