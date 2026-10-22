/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4986 : Family 10 := level10.get ⟨1585,by decide⟩
def sourceMap4986 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4986 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4986_checked : acceptsGraphIso
    (source (graph core4986) (root 10) 2 2) DegreeTwoThreeSpectrum7587.graph sourceMap4986=true := by decide +kernel
theorem fusedMap4986_checked : acceptsGraphIso
    (fused (graph core4986) (root 10) 2 2) DegreeTwoThreeSpectrum6074.graph fusedMap4986=true := by decide +kernel
theorem certified4986 : Certified (graph core4986) (root 10) 2 2 :=
  of_native_maps core4986 DegreeTwoThreeSpectrum7587.graph DegreeTwoThreeSpectrum6074.graph
    sourceMap4986 fusedMap4986 sourceMap4986_checked fusedMap4986_checked
    DegreeTwoThreeFiniteComparisons.comparison4986
#print axioms sourceMap4986_checked
#print axioms fusedMap4986_checked
#print axioms certified4986
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
