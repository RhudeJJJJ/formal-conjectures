/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4677 : Family 10 := level10.get ⟨817,by decide⟩
def sourceMap4677 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,16,7,8,9,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4677 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4677_checked : acceptsGraphIso
    (source (graph core4677) (root 10) 2 2) DegreeTwoThreeSpectrum7464.graph sourceMap4677=true := by decide +kernel
theorem fusedMap4677_checked : acceptsGraphIso
    (fused (graph core4677) (root 10) 2 2) DegreeTwoThreeSpectrum5619.graph fusedMap4677=true := by decide +kernel
theorem certified4677 : Certified (graph core4677) (root 10) 2 2 :=
  of_native_maps core4677 DegreeTwoThreeSpectrum7464.graph DegreeTwoThreeSpectrum5619.graph
    sourceMap4677 fusedMap4677 sourceMap4677_checked fusedMap4677_checked
    DegreeTwoThreeFiniteComparisons.comparison4677
#print axioms sourceMap4677_checked
#print axioms fusedMap4677_checked
#print axioms certified4677
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
