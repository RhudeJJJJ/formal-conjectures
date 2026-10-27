/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4622 : Family 10 := level10.get ⟨664,by decide⟩
def sourceMap4622 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,15,16,13,14,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4622 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4622_checked : acceptsGraphIso
    (source (graph core4622) (root 10) 2 2) DegreeTwoThreeSpectrum7315.graph sourceMap4622=true := by decide +kernel
theorem fusedMap4622_checked : acceptsGraphIso
    (fused (graph core4622) (root 10) 2 2) DegreeTwoThreeSpectrum5374.graph fusedMap4622=true := by decide +kernel
theorem certified4622 : Certified (graph core4622) (root 10) 2 2 :=
  of_native_maps core4622 DegreeTwoThreeSpectrum7315.graph DegreeTwoThreeSpectrum5374.graph
    sourceMap4622 fusedMap4622 sourceMap4622_checked fusedMap4622_checked
    DegreeTwoThreeFiniteComparisons.comparison4622
#print axioms sourceMap4622_checked
#print axioms fusedMap4622_checked
#print axioms certified4622
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
