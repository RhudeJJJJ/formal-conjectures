/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4847 : Family 10 := level10.get ⟨1246,by decide⟩
def sourceMap4847 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4847 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4847_checked : acceptsGraphIso
    (source (graph core4847) (root 10) 2 2) DegreeTwoThreeSpectrum7328.graph sourceMap4847=true := by decide +kernel
theorem fusedMap4847_checked : acceptsGraphIso
    (fused (graph core4847) (root 10) 2 2) DegreeTwoThreeSpectrum6481.graph fusedMap4847=true := by decide +kernel
theorem certified4847 : Certified (graph core4847) (root 10) 2 2 :=
  of_native_maps core4847 DegreeTwoThreeSpectrum7328.graph DegreeTwoThreeSpectrum6481.graph
    sourceMap4847 fusedMap4847 sourceMap4847_checked fusedMap4847_checked
    DegreeTwoThreeFiniteComparisons.comparison4847
#print axioms sourceMap4847_checked
#print axioms fusedMap4847_checked
#print axioms certified4847
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
