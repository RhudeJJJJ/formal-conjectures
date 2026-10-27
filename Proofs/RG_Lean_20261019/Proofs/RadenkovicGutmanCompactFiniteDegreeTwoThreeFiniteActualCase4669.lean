/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4669 : Family 10 := level10.get ⟨796,by decide⟩
def sourceMap4669 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4669 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4669_checked : acceptsGraphIso
    (source (graph core4669) (root 10) 2 2) DegreeTwoThreeSpectrum7456.graph sourceMap4669=true := by decide +kernel
theorem fusedMap4669_checked : acceptsGraphIso
    (fused (graph core4669) (root 10) 2 2) DegreeTwoThreeSpectrum5585.graph fusedMap4669=true := by decide +kernel
theorem certified4669 : Certified (graph core4669) (root 10) 2 2 :=
  of_native_maps core4669 DegreeTwoThreeSpectrum7456.graph DegreeTwoThreeSpectrum5585.graph
    sourceMap4669 fusedMap4669 sourceMap4669_checked fusedMap4669_checked
    DegreeTwoThreeFiniteComparisons.comparison4669
#print axioms sourceMap4669_checked
#print axioms fusedMap4669_checked
#print axioms certified4669
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
