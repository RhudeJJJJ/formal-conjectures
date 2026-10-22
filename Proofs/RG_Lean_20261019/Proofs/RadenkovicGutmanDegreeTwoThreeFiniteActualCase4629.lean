/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4629 : Family 10 := level10.get ⟨676,by decide⟩
def sourceMap4629 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4629 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4629_checked : acceptsGraphIso
    (source (graph core4629) (root 10) 2 2) DegreeTwoThreeSpectrum7309.graph sourceMap4629=true := by decide +kernel
theorem fusedMap4629_checked : acceptsGraphIso
    (fused (graph core4629) (root 10) 2 2) DegreeTwoThreeSpectrum5398.graph fusedMap4629=true := by decide +kernel
theorem certified4629 : Certified (graph core4629) (root 10) 2 2 :=
  of_native_maps core4629 DegreeTwoThreeSpectrum7309.graph DegreeTwoThreeSpectrum5398.graph
    sourceMap4629 fusedMap4629 sourceMap4629_checked fusedMap4629_checked
    DegreeTwoThreeFiniteComparisons.comparison4629
#print axioms sourceMap4629_checked
#print axioms fusedMap4629_checked
#print axioms certified4629
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
