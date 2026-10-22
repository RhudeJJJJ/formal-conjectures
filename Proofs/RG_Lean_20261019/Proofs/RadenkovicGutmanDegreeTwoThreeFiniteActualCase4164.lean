/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4164 : Family 8 := level8.get ⟨201,by decide⟩
def sourceMap4164 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4164 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4164_checked : acceptsGraphIso
    (source (graph core4164) (root 8) 2 2) DegreeTwoThreeSpectrum3774.graph sourceMap4164=true := by decide +kernel
theorem fusedMap4164_checked : acceptsGraphIso
    (fused (graph core4164) (root 8) 2 2) DegreeTwoThreeSpectrum2463.graph fusedMap4164=true := by decide +kernel
theorem certified4164 : Certified (graph core4164) (root 8) 2 2 :=
  of_native_maps core4164 DegreeTwoThreeSpectrum3774.graph DegreeTwoThreeSpectrum2463.graph
    sourceMap4164 fusedMap4164 sourceMap4164_checked fusedMap4164_checked
    DegreeTwoThreeFiniteComparisons.comparison4164
#print axioms sourceMap4164_checked
#print axioms fusedMap4164_checked
#print axioms certified4164
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
