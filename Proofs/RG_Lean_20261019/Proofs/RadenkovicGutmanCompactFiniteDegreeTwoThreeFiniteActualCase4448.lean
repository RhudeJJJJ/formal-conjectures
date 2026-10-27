/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4448 : Family 10 := level10.get ⟨92,by decide⟩
def sourceMap4448 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4448 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4448_checked : acceptsGraphIso
    (source (graph core4448) (root 10) 2 2) DegreeTwoThreeSpectrum6577.graph sourceMap4448=true := by decide +kernel
theorem fusedMap4448_checked : acceptsGraphIso
    (fused (graph core4448) (root 10) 2 2) DegreeTwoThreeSpectrum5013.graph fusedMap4448=true := by decide +kernel
theorem certified4448 : Certified (graph core4448) (root 10) 2 2 :=
  of_native_maps core4448 DegreeTwoThreeSpectrum6577.graph DegreeTwoThreeSpectrum5013.graph
    sourceMap4448 fusedMap4448 sourceMap4448_checked fusedMap4448_checked
    DegreeTwoThreeFiniteComparisons.comparison4448
#print axioms sourceMap4448_checked
#print axioms fusedMap4448_checked
#print axioms certified4448
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
