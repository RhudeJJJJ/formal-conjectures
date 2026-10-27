/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4615 : Family 10 := level10.get ⟨646,by decide⟩
def sourceMap4615 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4615 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4615_checked : acceptsGraphIso
    (source (graph core4615) (root 10) 2 2) DegreeTwoThreeSpectrum7304.graph sourceMap4615=true := by decide +kernel
theorem fusedMap4615_checked : acceptsGraphIso
    (fused (graph core4615) (root 10) 2 2) DegreeTwoThreeSpectrum5344.graph fusedMap4615=true := by decide +kernel
theorem certified4615 : Certified (graph core4615) (root 10) 2 2 :=
  of_native_maps core4615 DegreeTwoThreeSpectrum7304.graph DegreeTwoThreeSpectrum5344.graph
    sourceMap4615 fusedMap4615 sourceMap4615_checked fusedMap4615_checked
    DegreeTwoThreeFiniteComparisons.comparison4615
#print axioms sourceMap4615_checked
#print axioms fusedMap4615_checked
#print axioms certified4615
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
