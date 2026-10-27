/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4523 : Family 10 := level10.get ⟨363,by decide⟩
def sourceMap4523 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4523 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4523_checked : acceptsGraphIso
    (source (graph core4523) (root 10) 2 2) DegreeTwoThreeSpectrum6781.graph sourceMap4523=true := by decide +kernel
theorem fusedMap4523_checked : acceptsGraphIso
    (fused (graph core4523) (root 10) 2 2) DegreeTwoThreeSpectrum5652.graph fusedMap4523=true := by decide +kernel
theorem certified4523 : Certified (graph core4523) (root 10) 2 2 :=
  of_native_maps core4523 DegreeTwoThreeSpectrum6781.graph DegreeTwoThreeSpectrum5652.graph
    sourceMap4523 fusedMap4523 sourceMap4523_checked fusedMap4523_checked
    DegreeTwoThreeFiniteComparisons.comparison4523
#print axioms sourceMap4523_checked
#print axioms fusedMap4523_checked
#print axioms certified4523
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
