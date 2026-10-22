/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4828 : Family 10 := level10.get ⟨1200,by decide⟩
def sourceMap4828 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4828 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4828_checked : acceptsGraphIso
    (source (graph core4828) (root 10) 2 2) DegreeTwoThreeSpectrum7287.graph sourceMap4828=true := by decide +kernel
theorem fusedMap4828_checked : acceptsGraphIso
    (fused (graph core4828) (root 10) 2 2) DegreeTwoThreeSpectrum6377.graph fusedMap4828=true := by decide +kernel
theorem certified4828 : Certified (graph core4828) (root 10) 2 2 :=
  of_native_maps core4828 DegreeTwoThreeSpectrum7287.graph DegreeTwoThreeSpectrum6377.graph
    sourceMap4828 fusedMap4828 sourceMap4828_checked fusedMap4828_checked
    DegreeTwoThreeFiniteComparisons.comparison4828
#print axioms sourceMap4828_checked
#print axioms fusedMap4828_checked
#print axioms certified4828
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
