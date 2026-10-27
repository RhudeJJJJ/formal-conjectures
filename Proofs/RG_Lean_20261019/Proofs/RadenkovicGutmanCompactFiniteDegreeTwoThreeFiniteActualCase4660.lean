/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4660 : Family 10 := level10.get ⟨774,by decide⟩
def sourceMap4660 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4660 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4660_checked : acceptsGraphIso
    (source (graph core4660) (root 10) 2 2) DegreeTwoThreeSpectrum7444.graph sourceMap4660=true := by decide +kernel
theorem fusedMap4660_checked : acceptsGraphIso
    (fused (graph core4660) (root 10) 2 2) DegreeTwoThreeSpectrum5551.graph fusedMap4660=true := by decide +kernel
theorem certified4660 : Certified (graph core4660) (root 10) 2 2 :=
  of_native_maps core4660 DegreeTwoThreeSpectrum7444.graph DegreeTwoThreeSpectrum5551.graph
    sourceMap4660 fusedMap4660 sourceMap4660_checked fusedMap4660_checked
    DegreeTwoThreeFiniteComparisons.comparison4660
#print axioms sourceMap4660_checked
#print axioms fusedMap4660_checked
#print axioms certified4660
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
