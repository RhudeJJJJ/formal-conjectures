/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4844 : Family 10 := level10.get ⟨1229,by decide⟩
def sourceMap4844 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4844 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4844_checked : acceptsGraphIso
    (source (graph core4844) (root 10) 2 2) DegreeTwoThreeSpectrum7308.graph sourceMap4844=true := by decide +kernel
theorem fusedMap4844_checked : acceptsGraphIso
    (fused (graph core4844) (root 10) 2 2) DegreeTwoThreeSpectrum6433.graph fusedMap4844=true := by decide +kernel
theorem certified4844 : Certified (graph core4844) (root 10) 2 2 :=
  of_native_maps core4844 DegreeTwoThreeSpectrum7308.graph DegreeTwoThreeSpectrum6433.graph
    sourceMap4844 fusedMap4844 sourceMap4844_checked fusedMap4844_checked
    DegreeTwoThreeFiniteComparisons.comparison4844
#print axioms sourceMap4844_checked
#print axioms fusedMap4844_checked
#print axioms certified4844
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
