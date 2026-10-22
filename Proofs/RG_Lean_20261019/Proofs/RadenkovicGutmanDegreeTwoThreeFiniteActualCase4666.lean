/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4666 : Family 10 := level10.get ⟨791,by decide⟩
def sourceMap4666 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4666 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4666_checked : acceptsGraphIso
    (source (graph core4666) (root 10) 2 2) DegreeTwoThreeSpectrum7460.graph sourceMap4666=true := by decide +kernel
theorem fusedMap4666_checked : acceptsGraphIso
    (fused (graph core4666) (root 10) 2 2) DegreeTwoThreeSpectrum5576.graph fusedMap4666=true := by decide +kernel
theorem certified4666 : Certified (graph core4666) (root 10) 2 2 :=
  of_native_maps core4666 DegreeTwoThreeSpectrum7460.graph DegreeTwoThreeSpectrum5576.graph
    sourceMap4666 fusedMap4666 sourceMap4666_checked fusedMap4666_checked
    DegreeTwoThreeFiniteComparisons.comparison4666
#print axioms sourceMap4666_checked
#print axioms fusedMap4666_checked
#print axioms certified4666
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
