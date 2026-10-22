/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4678 : Family 10 := level10.get ⟨818,by decide⟩
def sourceMap4678 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,16,13,14,15,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4678 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4678_checked : acceptsGraphIso
    (source (graph core4678) (root 10) 2 2) DegreeTwoThreeSpectrum7467.graph sourceMap4678=true := by decide +kernel
theorem fusedMap4678_checked : acceptsGraphIso
    (fused (graph core4678) (root 10) 2 2) DegreeTwoThreeSpectrum5620.graph fusedMap4678=true := by decide +kernel
theorem certified4678 : Certified (graph core4678) (root 10) 2 2 :=
  of_native_maps core4678 DegreeTwoThreeSpectrum7467.graph DegreeTwoThreeSpectrum5620.graph
    sourceMap4678 fusedMap4678 sourceMap4678_checked fusedMap4678_checked
    DegreeTwoThreeFiniteComparisons.comparison4678
#print axioms sourceMap4678_checked
#print axioms fusedMap4678_checked
#print axioms certified4678
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
